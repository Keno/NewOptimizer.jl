module NewIR

using NotInferenceDontLookHere

struct Argument
    n::Int
end

struct PhiNode
    edges::Vector{Int}
    values::Vector{Any}
end
PhiNode() = PhiNode(Int[], Any[])

struct PiNode
    val::Any
    typ::Type
end

struct BasicBlock
    stmts::UnitRange{Int}
    preds::Vector{Int}
    succs::Vector{Int}
end
function BasicBlock(stmts::UnitRange{Int})
    BasicBlock(stmts, Int[], Int[])
end

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
    end
    expr
end

struct CFG
    blocks::Vector{BasicBlock}
    index::Vector{Int}
end

struct IRCode
    stmts::Vector{Any}
    types::Vector{Type}
    new_nodes::Vector{Tuple{Int, Type, Any}}
end
IRCode(stmts) = IRCode(stmts, Type[], Tuple{Int, Type, Any}[])

function scan_ssa_use!(used, stmt)
    isa(stmt, SSAValue) && push!(used, stmt.id)
    if isexpr(stmt, :call)
        foreach(arg->scan_ssa_use!(used, arg), stmt.args)
    elseif isa(stmt, GotoIfNot)
        scan_ssa_use!(used, stmt.cond)
    elseif isa(stmt, ReturnNode) || isa(stmt, PiNode)
        scan_ssa_use!(used, stmt.val)
    elseif isa(stmt, PhiNode)
        foreach(arg->scan_ssa_use!(used, arg), stmt.values)
    end
end

function scan_ssa_uses!(used, stmts)
    foreach(stmt->scan_ssa_use!(used, stmt), stmts)
end

function print_node(io::IO, idx, stmt, used, maxsize; color = true)
    if idx in used
        pad = " "^(maxsize-length(string(idx)))
        print(io, "%$idx $pad= ")
    else
        print(io, " "^(maxsize+4))
    end
    if isa(stmt, PhiNode)
        print(io, "φ ", '(', join(
            map(zip(stmt.edges, stmt.values)) do (e, v)
                sprint() do io′
                    print(io′, e, " => ")
                    print_ssa(io′, v)
                end
            end, ", "), ')')
    elseif isa(stmt, PiNode)
        print(io, "π (")
        print_ssa(io, stmt.val)
        print(io, ", ")
        if color
            printstyled(io, stmt.typ, color=:red)
        else
            print(io, stmt.typ)
        end
        print(io, ")")
    elseif isa(stmt, ReturnNode)
        print(io, "return ")
        print_ssa(io, stmt.val)
    elseif isa(stmt, GotoIfNot)
        print(io, "goto ", stmt.dest, " if not ")
        print_ssa(io, stmt.cond)
    elseif isexpr(stmt, :call)
        print_ssa(io, stmt.args[1])
        print(io, "(")
        print(io, join(map(arg->sprint(io->print_ssa(io, arg)), stmt.args[2:end]), ", "))
        print(io, ")")
        if stmt.typ !== Any
            print(io, "::$(stmt.typ)")
        end
    else
        print(io, stmt)
    end
end

print_ssa(io::IO, val) = isa(val, SSAValue) ? print(io, "%$(val.id)") : print(io, val)
function Base.show(io::IO, code::IRCode)
    used = Set{Int}()
    println(io, "Code")
    scan_ssa_uses!(used, code.stmts)
    foreach(((_a,_b,node),)->scan_ssa_use!(used, node), code.new_nodes)
    maxused = maximum(used)
    maxsize = length(string(maxused))
    cfg = compute_basic_blocks(code.stmts)
    bb_idx = 1
    new_nodes = Iterators.Stateful(sort(code.new_nodes, by = x->x[1]))
    for (idx, stmt) in enumerate(code.stmts)
        bbrange = cfg.blocks[bb_idx].stmts
        if idx != last(bbrange)
            if idx == first(bbrange)
                print(io, "┌ ")
            else
                print(io, "│ ")
            end
        end
        print_sep = false
        if idx == last(bbrange)
            print_sep = true
            bb_idx += 1
        end
        floop = true
        while !isempty(new_nodes) && Base.peek(new_nodes)[1] == idx
            _, typ, node = popfirst!(new_nodes)
            node_idx = length(code.stmts) + length(code.new_nodes) - length(new_nodes)
            if print_sep
                if floop
                    print(io, "┌ ")
                else
                    print(io, "│ ")
                end
            end
            print_sep = true
            floop = false
            Base.with_output_color(:yellow, io) do io′
                print_node(io′, node_idx, node, used, maxsize; color = false)
            end
            if !isa(node, PiNode) && node_idx in used
                printstyled(io, "::$(typ)", color=:red)
            end
            println(io)
        end
        if print_sep
            print(io, idx == last(bbrange) ? "└ " : "│ ")
        end
        print_node(io, idx, stmt, used, maxsize)
        if !isa(stmt, PiNode) && idx in used
            printstyled(io, "::$(code.types[idx])", color=:red)
        end
        println(io)
    end
end

function block_for_inst(index, inst)
    searchsortedfirst(index, inst, lt=(<=))
end
block_for_inst(cfg::CFG, inst) = block_for_inst(cfg.index, inst)

function compute_basic_blocks(stmts::Vector{Any})
    f = 1
    basic_block_index = Int[]
    blocks = BasicBlock[]
    # First go through and split statements into blocks
    for (idx, stmt) in pairs(stmts)
        # LabelNode starts a new BasicBlock
        if isa(stmt, LabelNode)
            if (f <= idx - 1)
                push!(blocks, BasicBlock(f:idx-1))
                push!(basic_block_index, idx)
            end
            f = idx
        # Terminators
        elseif isa(stmt, Union{GotoIfNot, GotoNode, ReturnNode})
            push!(blocks, BasicBlock(f:idx))
            f = idx + 1
            push!(basic_block_index, f)
        end
    end
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
            push!(blocks[num+1].preds, num)
            push!(b.succs, num+1)
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

function scan_entry!(result, idx, stmt)
    # NewVarNodes count as defs for the purpose
    # of liveness analysis (i.e. they kill use chains)
    if isa(stmt, NewvarNode)
        push!(result[slot_id(stmt.slot)].defs, idx)
    elseif isexpr(stmt, :(=))
        if isa(stmt.args[1], SlotNumber)
            push!(result[slot_id(stmt.args[1])].defs, idx)
        end
        scan_entry!(result, idx, stmt.args[2])
    elseif isexpr(stmt, :call)
        for arg in stmt.args
            (isa(arg, SlotNumber) || isa(arg, TypedSlot)) || continue
            push!(result[slot_id(arg)].uses, idx)
        end
    elseif isa(stmt, GotoIfNot)
        scan_entry!(result, idx, stmt.cond)
    elseif isa(stmt, SlotNumber) || isa(stmt, TypedSlot)
        push!(result[slot_id(stmt)].uses, idx)
    end
end

@inline slot_id(s) = isa(s, SlotNumber) ? (s::SlotNumber).id : (s::TypedSlot).id
function scan_slot_def_use(nargs, ci)
    nslots = length(ci.slotnames)
    result = [SlotInfo() for i = 1:nslots]
    # Set defs for arguments
    for var in result[1:(1+nargs)]
        push!(var.defs, 0)
    end
    for (idx, stmt) in enumerate(ci.code)
        scan_entry!(result, idx, stmt)
    end
    result
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
        return ReturnNode{Any}(fixup_use!(stmt.val))
    end
    if isexpr(stmt, :call)
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
    if isexpr(stmt, :call)
        for i = 1:length(stmt.args)
            stmt.args[i] = rename_uses!(stmt.args[i], renames)
        end
        return stmt
    end
    return stmt
end

function renumber_ssa!(stmt, ssanums, new_ssa=false, used_ssa = Set{Int}())
    if isa(stmt, SSAValue)
        id = stmt.id + (new_ssa ? 0 : 1)
        if id > length(ssanums)
            return stmt
        end
        val = ssanums[id]
        isa(val, SSAValue) && push!(used_ssa, val.id)
        return val
    end
    if isexpr(stmt, :(=))
        stmt.args[2] = renumber_ssa!(stmt.args[2], ssanums, new_ssa, used_ssa)
        return stmt
    end
    if isa(stmt, GotoIfNot)
        return GotoIfNot{Any}(renumber_ssa!(stmt.cond, ssanums, new_ssa, used_ssa), stmt.dest)
    elseif isa(stmt, ReturnNode)
        return ReturnNode{Any}(renumber_ssa!(stmt.val, ssanums, new_ssa, used_ssa))
    elseif isa(stmt, PhiNode)
        return PhiNode(stmt.edges, map(arg->renumber_ssa!(arg, ssanums, new_ssa, used_ssa), stmt.values))
    elseif isa(stmt, PiNode)
        return PiNode(renumber_ssa!(stmt.val, ssanums, new_ssa, used_ssa), stmt.typ)
    end
    if isexpr(stmt, :call)
        for i = 1:length(stmt.args)
            stmt.args[i] = renumber_ssa!(stmt.args[i], ssanums, new_ssa, used_ssa)
        end
        return stmt
    end
    return stmt
end

function make_ssa!(ci, idx, slot, typ)
    (idx == 0) && return Argument(slot)
    stmt = ci.code[idx]
    @assert isexpr(stmt, :(=))
    push!(ci.ssavaluetypes, typ)
    ssa = length(ci.ssavaluetypes)-1
    stmt.args[1] = SSAValue(ssa)
    ssa
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
    return typeof(val)
end

function construct_ssa!(ci, cfg, domtree, defuse)
    left = Int[]
    defuse_blocks = lift_defuse(cfg, defuse)
    phi_slots = [Vector{Int}() for _ = 1:length(cfg.blocks)]
    phi_nodes = [Vector{Pair{Int,PhiNode}}() for _ = 1:length(cfg.blocks)]
    phi_ssas = SSAValue[]
    code = Any[nothing for _ = 1:length(ci.code)]
    ir = IRCode(code)
    for (idx, slot) in enumerate(defuse)
        # No uses => no need for phi nodes
        isempty(slot.uses) && continue
        if length(slot.defs) == 1
            if slot.defs[] == 0
                typ = ci.slottypes[idx]
            else
                val = ci.code[slot.defs[]].args[2]
                typ = typ_for_val(val, ci)
            end
            ssaval = make_ssa!(ci, slot.defs[], idx, typ)
            fixup_uses!(ci, slot.uses, idx, ssaval)
            continue
        end
        # TODO: Perform liveness here to eliminate dead phi nodes
        phiblocks = idf(cfg, defuse_blocks, domtree, idx)
        for block in phiblocks
            push!(phi_slots[block], idx)
            node = PhiNode()
            ssa = insert_node!(ir, first_insert_for_bb(ci.code, cfg, block), Union{}, node)
            push!(phi_nodes[block], ssa.id=>node)
        end
        push!(left, idx)
    end
    # Perform SSA renaming
    worklist = Any[(1, 0, fill(SSAValue(-1), length(ci.slotnames)))]
    visited = Set{Int}()
    while true
        (item, pred, incoming_vals) = pop!(worklist)
        # Insert phi nodes if necessary
        for (idx, slot) in enumerate(phi_slots[item])
            ssaval, node = phi_nodes[item][idx]
            push!(node.edges, pred)
            incoming_val = incoming_vals[slot]
            push!(node.values, incoming_val)
            typ = typ_for_val(incoming_val, ci)
            new_node_id = ssaval - length(ir.stmts)
            old_insert, old_typ, _ = ir.new_nodes[new_node_id]
            ir.new_nodes[new_node_id] = (old_insert, Union{old_typ, typ}, node)
            incoming_vals[slot] = SSAValue(ssaval)
        end
        push!(visited, item)
        for idx in cfg.blocks[item].stmts
            stmt = ci.code[idx]
            if isa(stmt, NewvarNode)
                ci.code[idx] = nothing
                continue
            end
            # Rename any uses
            ci.code[idx] = rename_uses!(stmt, incoming_vals)
            # Record a store
            if isexpr(stmt, :(=)) && isa(stmt.args[1], SlotNumber)
                id = slot_id(stmt.args[1])
                val = stmt.args[2]
                typ = typ_for_val(val, ci)
                incoming_vals[id] = SSAValue(make_ssa!(ci, idx, id, typ))
            end
        end
        for succ in cfg.blocks[item].succs
            push!(worklist, (succ, item, copy(incoming_vals)))
        end
        isempty(worklist) && break
    end
    # Delete any instruction in unreachable blocks
    for bb in setdiff(Set{Int}(1:length(cfg.blocks)), visited)
        for idx in cfg.blocks[bb].stmts
            ci.code[idx] = nothing
        end
    end
    # Convert into IRCode form
    ssavalmap = fill(SSAValue(-1), length(ci.ssavaluetypes)+1)
    types = Type[Any for _ = 1:(length(code)+length(ir.new_nodes))]
    # Detect statement positions for assignments and construct array
    for (idx, stmt) in enumerate(ci.code)
        if isexpr(stmt, :(=)) && isa(stmt.args[1], SSAValue)
            @show stmt
            ssavalmap[stmt.args[1].id + 1] = SSAValue(idx)
            types[idx] = ci.ssavaluetypes[stmt.args[1].id + 1]
            code[idx] = stmt.args[2]
        else
            code[idx] = stmt
        end
    end
    # Renumber SSA values
    code = map(stmt->renumber_ssa!(stmt, ssavalmap), code)
    @show ir.new_nodes
    new_nodes = map(((pt,typ,stmt),)->(pt, typ, renumber_ssa!(stmt, ssavalmap)), ir.new_nodes)
    IRCode(code, types, new_nodes)
end

function is_call(stmt, sym)
    isexpr(stmt, :call) || return false
    isa(stmt.args[1], GlobalRef) || return false
    (stmt.args[1].name === sym) || return false
    return true
end

function stmt_effect_free(stmt)
    isa(stmt, PiNode) && return true
    isa(stmt, PhiNode) && return true
    return is_call(stmt, :tuple) || is_call(stmt, :getfield)
end

function process_node!(result, result_idx, ssa_rename, late_fixup, used_ssas, stmt, idx, keep_meta)
    if stmt === nothing
        # eliminate this node
    elseif !keep_meta && (isexpr(stmt, :meta) || isa(stmt, LineNumberNode))
        # eliminate this node
    elseif isexpr(stmt, :call) || isexpr(stmt, :invoke) || isa(stmt, ReturnNode)
        result[result_idx] = renumber_ssa!(stmt, ssa_rename, true, used_ssas)
        ssa_rename[idx] = SSAValue(result_idx)
        result_idx += 1
    elseif isa(stmt, GotoNode) || isa(stmt, LabelNode)
        target = stmt.label
        if target >= idx
            push!(late_fixup, result_idx)
            result[result_idx] = stmt
        else
            result[result_idx] = typeof(stmt)(ssa_rename[stmt.label].id)
        end
        ssa_rename[idx] = SSAValue(result_idx)
        result_idx += 1
    elseif isa(stmt, GotoIfNot)
        target = stmt.dest
        if target > idx
            push!(late_fixup, result_idx)
            result[result_idx] = GotoIfNot(renumber_ssa!(stmt.cond, ssa_rename, true, used_ssas), stmt.dest)
        else
            result[result_idx] = GotoIfNot(renumber_ssa!(stmt.cond, ssa_rename, true, used_ssas), ssa_rename[stmt.dest].id)
        end
        ssa_rename[idx] = SSAValue(result_idx)
        result_idx += 1
    elseif isa(stmt, SSAValue) || (!isa(stmt, Expr) && !isa(stmt, PhiNode) && !isa(stmt, PiNode))
        # Constant or identity assign, replace uses of this
        # ssa value with its result
        stmt = isa(stmt, SSAValue) ? ssa_rename[stmt.id] : stmt
        ssa_rename[idx] = stmt
    else
        result[result_idx] = renumber_ssa!(stmt, ssa_rename, true, used_ssas)
        ssa_rename[idx] = SSAValue(result_idx)
        result_idx += 1
    end
    return result_idx
end

function compact!(code::IRCode, keep_meta=false)
    # Sort nodes to insert. We'll insert them as we go along
    sort!(code.new_nodes, by=x->x[1])
    new_nodes = Iterators.Stateful(code.new_nodes)
    result = Array{Any}(uninitialized, length(code.stmts) + length(code.new_nodes))
    result_types = Array{Any}(uninitialized, length(code.stmts) + length(code.new_nodes))
    ssa_rename = Any[SSAValue(i) for i = 1:(length(code.stmts) + length(code.new_nodes))]
    result_idx = 1
    late_fixup = Int[]
    used_ssas = Set{Int}()
    for (idx, stmt) in pairs(code.stmts)
        while !isempty(new_nodes) && Base.peek(new_nodes)[1] == idx
            _, typ, new_node = popfirst!(new_nodes)
            new_idx = length(code.stmts) + length(code.new_nodes) - length(new_nodes)
            result_types[result_idx] = typ
            result_idx = process_node!(result, result_idx,
                ssa_rename, late_fixup, used_ssas, new_node, new_idx, keep_meta)
        end
        # This will get overwritten in future iterations if
        # result_idx is not, incremented, but that's ok and expected
        result_types[result_idx] = code.types[idx]
        result_idx = process_node!(result, result_idx, ssa_rename,
            late_fixup, used_ssas, stmt, idx, keep_meta)
    end
    for idx in late_fixup
        stmt = result[idx]
        if isa(stmt, GotoNode) || isa(stmt, LabelNode)
            result[idx] = typeof(stmt)(ssa_rename[stmt.label].id)
        elseif isa(stmt, GotoIfNot)
            result[idx] = GotoIfNot(stmt.cond, ssa_rename[stmt.dest].id)
        end
    end
    resize!(result, result_idx-1)
    resize!(result_types, result_idx-1)
    # Perform simple DCE for unused values
    for unused in setdiff(Set{Int}(1:length(result)), used_ssas)
        if stmt_effect_free(result[unused])
            result[unused] = nothing
        end
    end
    IRCode(result, result_types, Any[])
end

function value_typ(ir, value)
    isa(value, SSAValue) && return ir.types[value.id]
    isa(value, GlobalRef) && return typeof(getfield(value.mod, value.name))
    return typeof(value)
end

function getfield_elim_pass!(ir::IRCode)
    for (idx, stmt) in pairs(ir.stmts)
        is_call(stmt, :getfield) || continue
        isa(stmt.args[2], SSAValue) || continue
        isa(stmt.args[3], Int) || continue
        field_idx = stmt.args[3]
        defidx = stmt.args[2].id
        def = ir.stmts[defidx]
        typeconstraint = ir.types[defidx]
        phi_locs = Tuple{Int, Int}[]
        while true
            if isa(def, PiNode)
                typeconstraint = typeintersect(typeconstraint, def.typ)
                defidx = def.val.id
                def = ir.stmts[defidx]
                continue
            elseif isa(def, PhiNode)
                possible_predecessors = collect(Iterators.filter(zip(def.edges, def.values)) do (edge, value)
                    edge_typ = value_typ(ir, value)
                    return edge_typ <: typeconstraint
                end)
                # For now, only look at unique predecessors
                if length(possible_predecessors) == 1
                    pred, val = possible_predecessors[1]
                    push!(phi_locs, (pred, defidx))
                    defidx = val.id
                    def = ir.stmts[defidx]
                end
                continue
            end
            break
        end
        is_call(def, :tuple) || continue
        forwarded = def.args[1+field_idx]
        if isa(forwarded, SSAValue)
            forwarded_typ = ir.types[forwarded.id]
            for (pred, pos) in reverse!(phi_locs)
                node = PhiNode()
                push!(node.edges, pred)
                push!(node.values, forwarded)
                forwarded = insert_node!(ir, pos, forwarded_typ, node)
            end
        end
        ir.stmts[idx] = forwarded
        # For non-dominating load-store forward, we may have to insert extra phi nodes
        # TODO: Can use the domtree to eliminate unnecessary phis, but ok for now
    end
end

function get_def(ir::IRCode, val::SSAValue)
    ir.stmts[val.id]
end

function annotate_pred!(ir, cfg, domtree, root, val, replacement)
    for bb in dominated(domtree, root)
        for idx in cfg.blocks[bb].stmts
            # This is overkill, but this is only a prototype
            renumber = Any[SSAValue(n) for n = 1:length(ir.stmts)]
            renumber[val.id] = replacement
            ir.stmts[idx] = renumber_ssa!(ir.stmts[idx], renumber, true)
        end
    end
end

function insert_node!(ir::IRCode, pos, typ, val)
    push!(ir.new_nodes, (pos, typ, val))
    return SSAValue(length(ir.stmts) + length(ir.new_nodes))
end

function predicate_insertion_pass!(ir::IRCode, cfg, domtree)
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
        true_block = block_for_inst(cfg, idx + 1)
        false_block = block_for_inst(cfg, stmt.dest)
        true_val = insert_node!(ir, first_insert_for_bb(ir.stmts, cfg, true_block), true_type, PiNode(val, true_type))
        false_val = insert_node!(ir, first_insert_for_bb(ir.stmts, cfg, false_block), false_type, PiNode(val, false_type))
        annotate_pred!(ir, cfg, domtree, true_block, val, true_val)
        annotate_pred!(ir, cfg, domtree, false_block, val, false_val)
    end
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

function type_lift_pass!(ir::IRCode)
    type_ctx_uses = Vector{Vector{Int}}[]
    has_non_type_ctx_uses = Set{Int}()
    for (idx, stmt) in pairs(ir.stmts)
        x = get_val_if_type_cmp(stmt)
        x === nothing && continue
        val, cmp = x
        cmptyp = typeof(cmp)
        def = ir.stmts[val.id]
        @show def
        if isa(def, PhiNode)
            # See if this is only true on one branch
            branches = collect(Iterators.filter(zip(def.edges, def.values)) do (edge, value)
                @show value_typ(ir, value)
                cmptyp <: value_typ(ir, value)
            end)
            @show branches
            length(branches) == 1 || continue
            value_typ(ir, branches[1][2]) == cmptyp || continue
            # Ok, merge the compare into the phi node
            node = PhiNode()
            for edge in def.edges
                push!(node.edges, edge)
                push!(node.values, edge == branches[1][1])
            end
            ir.stmts[idx] = insert_node!(ir, val.id, Bool, node)
        end
    end
end

# Test Case
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
getfield_elim_pass!(ir)
@show ir
ir = compact!(compact!(ir))
type_lift_pass!(ir)
@show compact!(compact!(ir))

end
