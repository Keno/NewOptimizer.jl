function verify_ir(ir::IRCode)
    # For now require compact IR
    @assert isempty(ir.new_nodes)
    domtree = construct_domtree(ir.cfg)
    for (bb, idx, stmt) in bbidxstmt(ir)
        isa(stmt, PhiNode) && continue
        foreachssa(stmt) do op
            def_bb = block_for_inst(ir.cfg, op.id)
            if (def_bb == bb)
                @assert op.id < idx
            else
                if !dominates(domtree, def_bb, bb)
                    @show op
                    @error "Basic Block $def_bb does not dominate block $bb"
                end
            end
        end
    end
end