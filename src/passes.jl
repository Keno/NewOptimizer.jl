function getfield_elim_pass!(ir::IRCode)
    compact = IncrementalCompact(ir)
    insertions = Vector{Any}()
    for (idx, stmt) in compact
        is_call(stmt, :getfield) || continue
        isa(stmt.args[2], SSAValue) || continue
        field = stmt.args[3]
        isa(field, QuoteNode) && (field = field.value)
        isa(field, Union{Int, Symbol}) || continue
        orig_defidx = defidx = stmt.args[2].id
        def = compact[defidx]
        typeconstraint = types(compact)[defidx]
        phi_locs = Tuple{Int, Int}[]
        while true
            if isa(def, PiNode)
                typeconstraint = typeintersect(typeconstraint, def.typ)
                defidx = def.val.id
                def = compact[defidx]
                continue
            elseif isa(def, PhiNode)
                possible_predecessors = collect(Iterators.filter(zip(def.edges, def.values)) do (edge, value)
                    edge_typ = value_typ(compact, value)
                    return edge_typ <: typeconstraint
                end)
                # For now, only look at unique predecessors
                if length(possible_predecessors) == 1
                    pred, val = possible_predecessors[1]
                    push!(phi_locs, (pred, defidx))
                    defidx = val.id
                    def = compact[defidx]
                    continue
                end
            end
            break
        end
        if is_call(def, :tuple)
            forwarded = def.args[1+field]
        elseif isexpr(def, :new)
            typ = def.typ
            !typ.mutable || continue
            if isa(field, Symbol)
                field = Base.fieldindex(typ, field, false)
                field == 0 && continue
            end
            forwarded = def.args[1+field]
        else
            continue
        end
        if !isempty(phi_locs) && isa(forwarded, SSAValue)
            # TODO: We have have to use BB ids for phi_locs
            # to avoid index invalidation.
            push!(insertions, (idx, phi_locs))
        end
        compact[idx] = forwarded
    end
    ir = finish(compact)
    for (idx, phi_locs) in insertions
        # For non-dominating load-store forward, we may have to insert extra phi nodes
        # TODO: Can use the domtree to eliminate unnecessary phis, but ok for now
        forwarded = ir.stmts[idx]
        forwarded_typ = ir.types[forwarded.id]
        for (pred, pos) in reverse!(phi_locs)
            node = PhiNode()
            push!(node.edges, pred)
            push!(node.values, forwarded)
            forwarded = insert_node!(ir, pos, forwarded_typ, node)
        end
        ir.stmts[idx] = forwarded
    end
    ir
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
        if isa(def, PhiNode)
            # See if this is only true on one branch
            branches = collect(Iterators.filter(zip(def.edges, def.values)) do (edge, value)
                cmptyp <: value_typ(ir, value)
            end)
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
    ir
end
