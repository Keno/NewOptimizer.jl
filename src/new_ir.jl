using NotInferenceDontLookHere

struct Argument
    n::Int
end

#=
struct PhiNode
    edges::Vector{Int}
    values::Vector{Any}
end
=#
Core.PhiNode() = Core.PhiNode(Any[], Any[])

#=
struct PiNode
    val::Any
    typ::Type
end
=#

#Maybe:
#struct LabelNode
#    ninstrs::Int
#end
#const Stmt = Union{Call, PhiNode, GotoIfNot, GlobalRef, ReturnNode}

struct GotoIfNot{T}
    cond::T
    dest::Int
end

struct ReturnNode{T}
    val::T
end

using Base.Meta
function normalize(expr)
    if isexpr(expr, :gotoifnot)
        return GotoIfNot{Any}(expr.args...)
    elseif isexpr(expr, :return)
        return ReturnNode{Any}(expr.args...)
    elseif isa(expr, LabelNode)
        return nothing
    end
    expr
end

function block_for_inst(index, inst)
    searchsortedfirst(index, inst, lt=(<=))
end
block_for_inst(cfg::CFG, inst) = block_for_inst(cfg.index, inst)

function compute_basic_blocks(stmts::Vector{Any})
    jump_dests = Set{Int}(1)
    terminators = Vector{Int}()
    # First go through and compute jump destinations
    for (idx, stmt) in pairs(stmts)
        # Terminators
        if isa(stmt, Union{GotoIfNot, GotoNode, ReturnNode})
            push!(terminators, idx)
            isa(stmt, ReturnNode) && continue
            if isa(stmt, GotoIfNot)
                push!(jump_dests, idx+1)
                push!(jump_dests, stmt.dest)
            else
                push!(jump_dests, stmt.label)
            end
        end
    end
    bb_starts = sort(collect(jump_dests))
    for i = length(stmts):-1:1
        if stmts[i] != nothing
            push!(bb_starts, i+1)
            break
        end
    end
    # Compute ranges
    basic_block_index = Int[]
    blocks = map(zip(bb_starts, Iterators.drop(bb_starts, 1))) do (first, last)
        push!(basic_block_index, first)
        BasicBlock(StmtRange(first, last-1))
    end
    popfirst!(basic_block_index)
    # Compute successors/predecessors
    for (num, b) in pairs(blocks)
        terminator = stmts[last(b.stmts)]
        # Conditional Branch
        if isa(terminator, GotoIfNot)
            block′ = block_for_inst(basic_block_index, terminator.dest)
            push!(blocks[block′].preds, num)
            push!(b.succs, block′)
        end
        if isa(terminator, GotoNode)
            block′ = block_for_inst(basic_block_index, terminator.label)
            push!(blocks[block′].preds, num)
            push!(b.succs, block′)
        elseif !isa(terminator, ReturnNode)
            if num + 1 <= length(blocks)
                push!(blocks[num+1].preds, num)
                push!(b.succs, num+1)
            end
        end
    end
    CFG(blocks, basic_block_index)
end

struct SlotInfo
    defs::Vector{Int}
    uses::Vector{Int}
end
SlotInfo() = SlotInfo(Int[], Int[])

function lift_defuse(cfg, defuse)
    map(defuse) do slot
        SlotInfo(
            map(x->block_for_inst(cfg, x), slot.defs),
            map(x->block_for_inst(cfg, x), slot.uses)
        )
    end
end


# Run iterated dominance frontier
function idf(cfg, defuse, domtree, slot)
    # This should be a priority queue, but TODO - sorted array for now
    pq = [(n, domtree.nodes[n].level) for n in defuse[slot].defs]
    sort!(pq, by=x->x[2])
    phiblocks = Int[]
    processed = Set{Int}()
    while !isempty(pq)
        node, level = pop!(pq)
        worklist = Int[]
        visited = Set{Int}()
        push!(worklist, node)
        while !isempty(worklist)
            active = pop!(worklist)
            for succ in cfg.blocks[active].succs
                succ_level = domtree.nodes[succ].level
                succ_level > level && continue
                succ in processed && continue
                push!(processed, succ)
                # <- TODO: Use liveness here
                push!(phiblocks, succ)
                if !(succ in defuse[slot].defs)
                    push!(pq, (succ, succ_level))
                    sort!(pq, by=x->x[2])
                end
            end

            for child in domtree.nodes[active].children
                child in visited && continue
                push!(visited, child)
                push!(worklist, child)
            end
        end
    end
    phiblocks
end

function first_insert_for_bb(code, cfg, block)
    for idx in cfg.blocks[block].stmts
        stmt = code[idx]
        if !isa(stmt, LabelNode) && !isa(stmt, PhiNode)
            return idx
        end
    end
end

function typ_for_val(val, ci)
    isa(val, Expr) && return val.typ
    isa(val, GlobalRef) && return typeof(getfield(val.mod, val.name))
    isa(val, SSAValue) && return ci.ssavaluetypes[val.id+1]
    isa(val, NewSSAValue) && return Any # For now
    return typeof(val)
end

function is_call(stmt, sym)
    isexpr(stmt, :call) || return false
    isa(stmt.args[1], GlobalRef) || return false
    (stmt.args[1].name === sym) || return false
    return true
end

function stmt_effect_free(stmt, src, mod)
    isa(stmt, Union{PiNode, PhiNode}) && return true
    isa(stmt, Union{ReturnNode, PhiNode, GotoNode, GotoIfNot}) && return false
    NI.statement_effect_free(stmt, src, mod)
end

function get_def(ir::IRCode, val::SSAValue)
    ir.stmts[val.id]
end

function annotate_pred!(ir, cfg, domtree, root, val, replacement)
    for bb in dominated(domtree, root)
        for idx in cfg.blocks[bb].stmts
            ir.stmts[idx] = ssamap(ir.stmts[idx]) do use
                use.id == val.id ? replacement : use
            end
        end
    end
end

function insert_node!(ir::IRCode, pos, typ, val)
    push!(ir.new_nodes, (pos, typ, val))
    return SSAValue(length(ir.stmts) + length(ir.new_nodes))
end

function predicate_insertion_pass!(ir::IRCode, domtree)
    cfg = ir.cfg
    for (idx, stmt) in pairs(ir.stmts)
        !isa(stmt, GotoIfNot) && continue
        !isa(stmt.cond, SSAValue) && continue
        def = get_def(ir, stmt.cond)
        is_call(def, :(===)) || continue
        (val, cmp) = def.args[2:3]
        if !isa(val, SSAValue)
            (cmp, val) = (val, cmp)
        end
        isa(val, SSAValue) || continue
        isa(cmp, SSAValue) && continue
        if isa(cmp, GlobalRef)
            cmp = getfield(cmp.mod, cmp.name)
        end
        isdefined(typeof(cmp), :instance) || continue
        true_type = typeof(cmp)
        false_type = Core.Compiler.typesubtract(ir.types[val.id], typeof(cmp))
        true_block = block_for_inst(cfg, idx) + 1
        false_block = stmt.dest
        true_val = insert_node!(ir, first_insert_for_bb(ir.stmts, cfg, true_block), true_type, PiNode(val, true_type))
        false_val = insert_node!(ir, first_insert_for_bb(ir.stmts, cfg, false_block), false_type, PiNode(val, false_type))
        annotate_pred!(ir, cfg, domtree, true_block, val, true_val)
        annotate_pred!(ir, cfg, domtree, false_block, val, false_val)
    end
    ir
end

function get_val_if_type_cmp(def)
    is_call(def, :(===)) || return nothing
    (val, cmp) = def.args[2:3]
    if !isa(val, SSAValue)
        (cmp, val) = (val, cmp)
    end
    isa(val, SSAValue) || return nothing
    isa(cmp, SSAValue) && return nothing
    if isa(cmp, GlobalRef)
        cmp = getfield(cmp.mod, cmp.name)
    end
    isdefined(typeof(cmp), :instance) || return nothing
    return (val, cmp)
end

function run_passes(ci::CodeInfo, mod::Module, nargs::Int)
    ccall(:jl_, Cvoid, (Any,), ci.code)
    ci.code = map(normalize, ci.code)
    ci.code = strip_trailing_junk(ci.code)
    cfg = compute_basic_blocks(ci.code)
    defuse_insts = scan_slot_def_use(nargs, ci)
    domtree = construct_domtree(cfg)
    ir = construct_ssa!(ci, mod, cfg, domtree, defuse_insts)
    ir = compact!(ir)
    verify_ir(ir)
    ir = predicate_insertion_pass!(ir, domtree)
    ir = compact!(ir)
    ir = getfield_elim_pass!(ir)
    ir = compact!(ir)
    ir = type_lift_pass!(ir)
    ir = compact!(ir)
    @show ("final", ir)
    ir
end

function construct_ssa(f, args, mod::Module=Core.Main)
    ci = NI.code_typed(f, args)[1].first
    ci.code = map(normalize, ci.code)
    ci.code = strip_trailing_junk(ci.code)
    cfg = compute_basic_blocks(ci.code)
    defuse_insts = scan_slot_def_use(nargs, ci)
    domtree = construct_domtree(cfg)
    ir = construct_ssa!(ci, mod, cfg, domtree, defuse_insts)
    ir
end

function run_passes(f, args, mod::Module=Core.Main)
    ci = NI.code_typed(f, args)[1].first
    run_passes(ci, mod,  length(args.parameters))
end

function run_passes_ci(f, args)
    ci = NI.code_typed(f, args)[1].first
    ir = run_passes(ci, length(args.parameters))
    replace_code!(ci, ir, length(args.parameters))
    ci
end
