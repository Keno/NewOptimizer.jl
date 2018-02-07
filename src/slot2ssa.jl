function scan_entry!(result, idx, stmt)
    # NewVarNodes count as defs for the purpose
    # of liveness analysis (i.e. they kill use chains)
    if isa(stmt, NewvarNode)
        push!(result[slot_id(stmt.slot)].defs, idx)
        return
    elseif isexpr(stmt, :(=))
        if isa(stmt.args[1], SlotNumber)
            push!(result[slot_id(stmt.args[1])].defs, idx)
        end
        stmt = stmt.args[2]
    end
    if isa(stmt, Union{SlotNumber, TypedSlot})
        push!(result[slot_id(stmt)].uses, idx)
        return
    end
    for op in userefs(stmt)
        val = op[]
        if isa(val, Union{SlotNumber, TypedSlot})
            push!(result[slot_id(val)].uses, idx)
        end
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

function new_to_regular(stmt)
    if isa(stmt, NewSSAValue)
        return SSAValue(stmt.id)
    end
    urs = userefs(stmt)
    urs === () && return stmt
    for op in urs
        val = op[]
        if isa(val, NewSSAValue)
            op[] = SSAValue(val.id)
        end
    end
    urs[]
end


function fixup_use!(stmt, slot, ssa)
    (isa(stmt, SlotNumber) || isa(stmt, TypedSlot)) && slot_id(stmt) == slot && return ssa
    if isexpr(stmt, :(=))
        stmt.args[2] = fixup_use!(stmt.args[2], slot, ssa)
        return stmt
    end
    urs = userefs(stmt)
    urs === () && return stmt
    for op in urs
        val = op[]
        if isa(val, Union{SlotNumber, TypedSlot}) && slot_id(val) == slot
            op[] = ssa
        end
    end
    urs[]
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
    urs = userefs(stmt)
    urs === () && return stmt
    for op in urs
        val = op[]
        if isa(val, Union{SlotNumber, TypedSlot})
            op[] = renames[slot_id(val)]
        end
    end
    urs[]
end

# Remove `nothing`s at the end, we don't handle them well
# (we expect the last instruction to be a terminator)
function strip_trailing_junk(code)
     for i = length(code):-1:1
         if code[i] !== nothing && !isexpr(code[i], :meta) &&
            !isa(code[i], LineNumberNode) && !isexpr(code[i], :line)
             resize!(code, i)
             break
         end
     end
     return code
end

function construct_ssa!(ci, mod, cfg, domtree, defuse)
    left = Int[]
    defuse_blocks = lift_defuse(cfg, defuse)
    phi_slots = [Vector{Int}() for _ = 1:length(cfg.blocks)]
    phi_nodes = [Vector{Pair{Int,PhiNode}}() for _ = 1:length(cfg.blocks)]
    phi_ssas = SSAValue[]
    code = Any[nothing for _ = 1:length(ci.code)]
    ir = IRCode(code, cfg, mod)
    for (idx, slot) in enumerate(defuse)
        # No uses => no need for phi nodes
        isempty(slot.uses) && continue
        if length(slot.defs) == 1
            if slot.defs[] == 0
                typ = ci.slottypes[idx]
                ssaval = Argument(idx)
            elseif isa(ci.code[slot.defs[]], NewvarNode)
                typ = Undef
                ssaval = undef_token
            else
                val = ci.code[slot.defs[]].args[2]
                typ = typ_for_val(val, ci)
                ssaval = SSAValue(make_ssa!(ci, slot.defs[], idx, typ))
            end
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
    worklist = Any[(1, 0, Any[((0 in defuse[x].defs) ? Argument(x) : SSAValue(-1)) for x = 1:length(ci.slotnames)])]
    visited = Set{Int}()
    while !isempty(worklist)
        (item, pred, incoming_vals) = pop!(worklist)
        # Insert phi nodes if necessary
        for (idx, slot) in enumerate(phi_slots[item])
            ssaval, node = phi_nodes[item][idx]
            push!(node.edges, pred)
            incoming_val = incoming_vals[slot]
            if incoming_val == SSAValue(-1)
                # Optimistically omit this path.
                # Liveness analysis would probably have prevented us from inserting this phi node
                continue
            end
            if incoming_val == undef_token
                resize!(node.values, length(node.values)+1)
            else
                push!(node.values, incoming_val)
            end
            typ = incoming_val == undef_token ? Undef : typ_for_val(incoming_val, ci)
            new_node_id = ssaval - length(ir.stmts)
            old_insert, old_typ, _ = ir.new_nodes[new_node_id]
            ir.new_nodes[new_node_id] = (old_insert, NI.tmerge(old_typ, typ), node)
            incoming_vals[slot] = NewSSAValue(ssaval)
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
    types = Any[Any for _ = 1:(length(code)+length(ir.new_nodes))]
    # Detect statement positions for assignments and construct array
    for (idx, stmt) in enumerate(ci.code)
        if isexpr(stmt, :(=)) && isa(stmt.args[1], SSAValue)
            ssavalmap[stmt.args[1].id + 1] = SSAValue(idx)
            types[idx] = ci.ssavaluetypes[stmt.args[1].id + 1]
            stmt = stmt.args[2]
            if isa(stmt, PhiNode)
                edges = map(stmt.edges) do edge
                    block_for_inst(cfg, edge)
                end
                code[idx] = PhiNode(convert(Vector{Any}, edges), stmt.values)
            else
                code[idx] = stmt
            end
        # Convert GotoNode/GotoIfNot/PhiNode to BB addressing
        elseif isa(stmt, GotoNode)
            code[idx] = GotoNode(block_for_inst(cfg, stmt.label))
        elseif isa(stmt, GotoIfNot)
            code[idx] = GotoIfNot{Any}(stmt.cond, block_for_inst(cfg, stmt.dest))
        else
            code[idx] = stmt
        end
    end
    # Renumber SSA values
    code = map(stmt->new_to_regular(renumber_ssa!(stmt, ssavalmap)), code)
    new_nodes = map(((pt,typ,stmt),)->(pt, typ, new_to_regular(renumber_ssa!(stmt, ssavalmap))), ir.new_nodes)
    IRCode(code, types, cfg, new_nodes, mod)
end
