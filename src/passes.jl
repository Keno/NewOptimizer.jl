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
                if isa(def.val, SSAValue)
                    defidx = def.val.id
                    def = compact[defidx]
                else
                    def = def.val
                end
                continue
            elseif isa(def, PhiNode)
                possible_predecessors = collect(Iterators.filter(1:length(def.edges)) do n
                    isassigned(def.values, n) || return false
                    value = def.values[n]
                    edge_typ = value_typ(compact, value)
                    return edge_typ <: typeconstraint
                end)
                # For now, only look at unique predecessors
                if length(possible_predecessors) == 1
                    n = possible_predecessors[1]
                    pred = def.edges[n]
                    val = def.values[n]
                    if isa(val, SSAValue)
                        push!(phi_locs, (pred, defidx))
                        defidx = val.id
                        def = compact[defidx]
                    else
                        def = val
                    end
                    continue
                end
            end
            break
        end
        if is_call(def, :tuple) && isa(field, Int) && 1 <= field < length(def.args)
            forwarded = def.args[1+field]
        elseif isexpr(def, :new)
            typ = def.typ
            if isa(typ, UnionAll)
                typ = Base.unwrap_unionall(typ)
            end
            isa(typ, DataType) || continue
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
    lifted_undef = Dict{Int, SSAValue}()
    for (idx, stmt) in pairs(ir.stmts)
        if isexpr(stmt, :isdefined) || isexpr(stmt, :undefcheck)
            val = isexpr(stmt, :isdefined) ? stmt.args[1] : stmt.args[2]
            # undef can only show up by being introduced in a phi
            # node, so lift all phi nodes that have maybe undef values
            processed = Dict{Int, Tuple{SSAValue, PhiNode}}()
            worklist = Tuple{Int, Int, Int}[(val.id, 0, 0)]
            stmt_id = val.id
            while isa(ir.stmts[stmt_id], PiNode)
                stmt_id = ir.stmts[stmt_id].val.id
            end
            if !haskey(lifted_undef, stmt_id)
                def = ir.stmts[stmt_id]
                first = true
                while !isempty(worklist)
                    item, which, use = pop!(worklist)
                    edges = copy(def.edges)
                    values = Vector{Any}(uninitialized, length(edges))
                    new_phi = insert_node!(ir, item, Bool, PhiNode(edges, values))
                    if first
                        lifted_undef[stmt_id] = new_phi
                        first = false
                    end
                    for i = 1:length(edges)
                        if !isassigned(def.values, i)
                            val = false
                        elseif !isa(def.values[i], SSAValue)
                            val = true
                        else
                            id = def.values[i].id
                            if !isa(ir.types[id], NI.MaybeUndef)
                                val = true
                            else
                                while isa(ir.stmts[id], PiNode)
                                    ir = ir.stmts[id].val.id
                                end
                                if isa(ir.stmts[id], PhiNode)
                                    if haskey(processed, id)
                                        val = processed[id][2]
                                    else
                                        push!(worklist, (id, new_phi, i))
                                        continue
                                    end
                                else
                                    val = true
                                end
                            end
                        end
                        values[i] = val
                    end
                    if which !== 0
                        ir[which].values[use] = new_phi
                    end
                end
            end
            if isexpr(stmt, :isdefiend)
                ir.stmts[idx] = lifted_undef[stmt_id]
            else
                ir.stmts[idx] = Expr(:throw_undef_if_not, stmt.args[1], lifted_undef[stmt_id])
            end
        else
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
    end
    ir
end
