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

struct DomTreeNode
    level::Int
    children::Vector{Int}
end
DomTreeNode() = DomTreeNode(1, Vector{Int}())

struct DomTree
    idoms::Vector{Int}
    nodes::Vector{DomTreeNode}
end

function update_level!(domtree, node, level)
    domtree[node] = DomTreeNode(level, domtree[node].children)
    foreach(domtree[node].children) do child
        update_level!(domtree, child, level+1)
    end
end

struct DominatedBlocks
    domtree::DomTree
    worklist::Vector{Int}
end

function dominated(domtree::DomTree, root::Int)
    doms = DominatedBlocks(domtree, Vector{Int}())
    push!(doms.worklist, root)
    doms
end

function Base.start(doms::DominatedBlocks)
    nothing
end

function Base.next(doms::DominatedBlocks, state::Nothing)
    bb = pop!(doms.worklist)
    for dominated in doms.domtree.nodes[bb].children
        push!(doms.worklist, dominated)
    end
    (bb, nothing)
end

function Base.done(doms::DominatedBlocks, state::Nothing)
    isempty(doms.worklist)
end

# Construct Dom Tree
# Simple algorithm - TODO: Switch to the fast version (e.g. https://tanujkhattar.wordpress.com/2016/01/11/dominator-tree-of-a-directed-graph/)
function construct_domtree(cfg)
    dominators = Set{Int}[n == 1 ? Set{Int}(n) : Set{Int}(1:length(cfg.blocks)) for n = 1:length(cfg.blocks)]
    changed = true
    while changed
        changed = false
        for n = 2:length(cfg.blocks)
            isempty(cfg.blocks[n].preds) && continue
            new_doms = union(Set{Int}(n), intersect(
                (dominators[p] for p in cfg.blocks[n].preds)...
            ))
            changed |= (new_doms != dominators[n])
            dominators[n] = new_doms
        end
    end
    # Compute idoms
    idoms = fill(0, length(cfg.blocks))
    for i = 2:length(cfg.blocks)
        for dom in dominators[i]
            i == dom && continue
            any(p->p !== i && p !== dom && dom in dominators[p], dominators[i]) && continue
            idoms[i] = dom
        end
    end
    # Compute children
    domtree = [DomTreeNode() for _ = 1:length(cfg.blocks)]
    for (idx, idom) in enumerate(idoms)
        (idx == 1 || idom == 0) && continue
        push!(domtree[idom].children, idx)
    end
    # Recursively set level
    update_level!(domtree, 1, 1)
    DomTree(idoms, domtree)
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

function fixup_use!(stmt, slot, ssa)
    ((isa(stmt, SlotNumber) || isa(stmt, TypedSlot)) && slot_id(stmt) == slot) && return isa(ssa, Int) ? SSAValue(ssa) : ssa
    if isexpr(stmt, :(=))
        stmt.args[2] = fixup_use!(stmt.args[2], slot, ssa)
        return stmt
    end
    if isa(stmt, GotoIfNot)
        return GotoIfNot{Any}(fixup_use!(stmt.cond, slot, ssa), stmt.dest)
    elseif isa(stmt, ReturnNode)
        return ReturnNode{Any}(fixup_use!(stmt.val, slot, ssa))
    end
    if isexpr(stmt, :call) || isexpr(stmt, :invoke) || isexpr(stmt, :new) ||
       isexpr(stmt, :gc_preserve_begin) || isexpr(stmt, :gc_preserve_end) || isexpr(stmt, :foreigncall)
        for i = 1:length(stmt.args)
            stmt.args[i] = fixup_use!(stmt.args[i], slot, ssa)
        end
        return stmt
    end
    return stmt
end

function fixup_uses!(ci, uses, slot, ssa)
    for use in uses
        ci.code[use] = fixup_use!(ci.code[use], slot, ssa)
    end
end

function rename_uses!(stmt, renames)
    (isa(stmt, SlotNumber) || isa(stmt, TypedSlot)) && return renames[slot_id(stmt)]
    if isexpr(stmt, :(=))
        stmt.args[2] = rename_uses!(stmt.args[2], renames)
        return stmt
    end
    if isa(stmt, GotoIfNot)
        return GotoIfNot{Any}(rename_uses!(stmt.cond, renames), stmt.dest)
    elseif isa(stmt, ReturnNode)
        return ReturnNode{Any}(rename_uses!(stmt.val, renames))
    end
    if isexpr(stmt, :call) || isexpr(stmt, :invoke) || isexpr(stmt, :new) ||
       isexpr(stmt, :gc_preserve_begin) || isexpr(stmt, :gc_preserve_end) || isexpr(stmt, :foreigncall)
        for i = 1:length(stmt.args)
            stmt.args[i] = rename_uses!(stmt.args[i], renames)
        end
        return stmt
    end
    return stmt
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
    @show ci.code
    ci.code = map(normalize, ci.code)
    cfg = compute_basic_blocks(ci.code)
    @show cfg
    defuse_insts = scan_slot_def_use(nargs, ci)
    domtree = construct_domtree(cfg)
    ir = construct_ssa!(ci, mod, cfg, domtree, defuse_insts)
    @show ("construct", ir)
    ir = compact!(ir)
    ir = predicate_insertion_pass!(ir, domtree)
    @show ("post_pred", ir)
    ir = compact!(ir)
    ir = getfield_elim_pass!(ir)
    ir = compact!(ir)
    ir = type_lift_pass!(ir)
    @show ("final_compact", ir)
    ir = compact!(ir)
    ir
end

function run_passes(f, args)
    ci = NI.code_typed(f, args)[1].first
    run_passes(ci, length(args.parameters))
end

function run_passes_ci(f, args)
    ci = NI.code_typed(f, args)[1].first
    ir = run_passes(ci, length(args.parameters))
    replace_code!(ci, ir, length(args.parameters))
    ci
end

# Test Case
#=
@noinline foo() = rand(Bool) ? 2 : nothing
@inline baz(x) = x ? (foo(), 1) : nothing
function bar(arg)
   x = baz(arg)
   x === nothing && return 0
   a, b = x
   a === nothing && return 1
   return a
end


# Workspace
ci = NI.code_typed(bar, Tuple{Bool})[1].first
ci.code = map(normalize, ci.code)
cfg = compute_basic_blocks(ci.code)
defuse_insts = scan_slot_def_use(1, ci)
domtree = construct_domtree(cfg)

@show defuse_insts

@show ci.code
ir = construct_ssa!(ci, cfg, domtree, defuse_insts)
@show ir
ir = compact!(ir)
@show ir
predicate_insertion_pass!(ir, compute_basic_blocks(ir.stmts), domtree)
@show ("predicate", ir)
ir = compact!(ir)
ir = getfield_elim_pass!(ir)
ir = compact!(ir)
ir = type_lift_pass!(ir)
@show compact!(ir)
=#
