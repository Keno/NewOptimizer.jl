function check_op(ir, domtree, op, use_bb, use_idx)
    if isa(op, SSAValue)
        def_bb = block_for_inst(ir.cfg, op.id)
        if (def_bb == use_bb)
            @assert op.id < use_idx
        else
            if !dominates(domtree, def_bb, use_bb)
                @show op
                @error "Basic Block $def_bb does not dominate block $use_bb"
                error()
            end
        end
    elseif isa(op, Union{SlotNumber, TypedSlot})
        @error "Left over slot detected in converted IR"
        error()
    end
end

function verify_ir(ir::IRCode)
    # For now require compact IR
    @assert isempty(ir.new_nodes)
    domtree = construct_domtree(ir.cfg)
    for (bb, idx, stmt) in bbidxstmt(ir)
        if isa(stmt, PhiNode)
            @assert length(stmt.edges) == length(stmt.values)
            for i = 1:length(stmt.edges)
                isassigned(stmt.values, i) || continue
                val = stmt.values[i]
                phiT = ir.types[idx]
                if isa(val, SSAValue)
                    #=
                    if !(NI.:⊑)(ir.types[val.id], phiT)
                        ccall(:jl_, Cvoid, (Any,), (idx, val.id, phiT, ir.types[val.id]))
                        ccall(:jl_, Cvoid, (Any,), ir.stmts)
                        #@show ir
                        @error """
                            PhiNode $idx, has operand $(val.id), whose type is not a sub lattice element.
                            PhiNode type was $phiT
                            Value type was $(ir.types[val.id])
                        """
                        error()
                    end
                    =#
                end
                check_op(ir, domtree, val, stmt.edges[i], last(ir.cfg.blocks[stmt.edges[i]].stmts)+1)
            end
        else
            for op in userefs(stmt)
                op = op[]
                check_op(ir, domtree, op, bb, idx)
            end
        end
    end
end
