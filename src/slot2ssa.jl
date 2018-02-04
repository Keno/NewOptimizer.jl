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
    elseif isexpr(stmt, :call) || isexpr(stmt, :new)
        for arg in stmt.args
            (isa(arg, SlotNumber) || isa(arg, TypedSlot)) || continue
            push!(result[slot_id(arg)].uses, idx)
        end
    elseif isa(stmt, GotoIfNot)
        scan_entry!(result, idx, stmt.cond)
    elseif isa(stmt, ReturnNode)
        scan_entry!(result, idx, stmt.val)
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

function renumber_ssa(stmt::SSAValue, ssanums, new_ssa=false, used_ssa = nothing)
    id = stmt.id + (new_ssa ? 0 : 1)
    if id > length(ssanums)
        return stmt
    end
    val = ssanums[id]
    if isa(val, SSAValue) && used_ssa !== nothing
        used_ssa[val.id] += 1
    end
    return val
end

function renumber_ssa!(stmt, ssanums, new_ssa=false, used_ssa = nothing)
    isa(stmt, SSAValue) && return renumber_ssa(stmt, ssanums, new_ssa, used_ssa)
    return ssamap(val->renumber_ssa(val, ssanums, new_ssa, used_ssa), stmt)
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

mutable struct Undef
let unconstructable; end
end

struct UndefToken
end
const undef_token = UndefToken()

function construct_ssa!(ci, cfg, domtree, defuse)
    left = Int[]
    defuse_blocks = lift_defuse(cfg, defuse)
    phi_slots = [Vector{Int}() for _ = 1:length(cfg.blocks)]
    phi_nodes = [Vector{Pair{Int,PhiNode}}() for _ = 1:length(cfg.blocks)]
    phi_ssas = SSAValue[]
    code = Any[nothing for _ = 1:length(ci.code)]
    ir = IRCode(code, cfg)
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
    worklist = Any[(1, 0, Any[SSAValue(-1) for _ = 1:length(ci.slotnames)])]
    visited = Set{Int}()
    while !isempty(worklist)
        (item, pred, incoming_vals) = pop!(worklist)
        # Insert phi nodes if necessary
        for (idx, slot) in enumerate(phi_slots[item])
            ssaval, node = phi_nodes[item][idx]
            push!(node.edges, pred)
            incoming_val = incoming_vals[slot]
            if incoming_val == undef_token
                resize!(node.values, length(node.values)+1)
            else
                push!(node.values, incoming_val)
            end
            typ = incoming_val == undef_token ? Undef : typ_for_val(incoming_val, ci)
            new_node_id = ssaval - length(ir.stmts)
            old_insert, old_typ, _ = ir.new_nodes[new_node_id]
            ir.new_nodes[new_node_id] = (old_insert, Union{old_typ, typ}, node)
            incoming_vals[slot] = SSAValue(ssaval)
        end
        (item in visited) && continue
        push!(visited, item)
        for idx in cfg.blocks[item].stmts
            stmt = ci.code[idx]
            # Rename any uses
            ci.code[idx] = rename_uses!(stmt, incoming_vals)
            # Record a store
            if isexpr(stmt, :(=)) && isa(stmt.args[1], SlotNumber)
                id = slot_id(stmt.args[1])
                val = stmt.args[2]
                typ = typ_for_val(val, ci)
                incoming_vals[id] = SSAValue(make_ssa!(ci, idx, id, typ))
            elseif isa(stmt, NewvarNode)
                incoming_vals[slot_id(stmt.slot)] = undef_token
                ci.code[idx] = nothing
            end
        end
        for succ in cfg.blocks[item].succs
            push!(worklist, (succ, item, copy(incoming_vals)))
        end
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
            ssavalmap[stmt.args[1].id + 1] = SSAValue(idx)
            types[idx] = ci.ssavaluetypes[stmt.args[1].id + 1]
            code[idx] = stmt.args[2]
        # Convert GotoNode/GotoIfNot to BB addressing
        elseif isa(stmt, GotoNode)
            code[idx] = GotoNode(block_for_inst(cfg, stmt.label))
        elseif isa(stmt, GotoIfNot)
            code[idx] = GotoIfNot{Any}(stmt.cond, block_for_inst(cfg, stmt.dest))
        else
            code[idx] = stmt
        end
    end
    # Renumber SSA values
    code = map(stmt->renumber_ssa!(stmt, ssavalmap), code)
    new_nodes = map(((pt,typ,stmt),)->(pt, typ, renumber_ssa!(stmt, ssavalmap)), ir.new_nodes)
    IRCode(code, types, cfg, new_nodes)
end