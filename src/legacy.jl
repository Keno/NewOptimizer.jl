function ssaargmap(f, stmt)
    urs = userefs(stmt)
    for op in urs
        val = op[]
        if isa(val, Union{SSAValue, Argument})
            op[] = f(val)
        end
    end
    urs[]
end

function replace_code!(ci::CodeInfo, code::IRCode, nargs)
    cfg = compute_basic_blocks(code.stmts)
    if !isempty(code.new_nodes)
        code = compact!(code)
    end
    # All but the first `nargs` slots will now be unused
    resize!(ci.slottypes, nargs+1)
    resize!(ci.slotnames, nargs+1)
    resize!(ci.slotflags, nargs+1)
    # For every used SSAValues, we register one base format ssa value
    used = Set{Int}()
    foreach(stmt->scan_ssa_use!(used, stmt), code.stmts)
    mapping = Dict{Int, Int}()
    n = 0
    resize!(ci.ssavaluetypes, length(used))
    for ssa in sort(collect(used))
        mapping[ssa] = n
        n += 1
        ci.ssavaluetypes[n] = code.types[ssa]
    end
    # Find all jump targets (we need to insert LabelNodes for them) and
    # jump origins (we insert a label node on the statement after, to
    # make sure we can track them)
    dest_blocks = Set{Int}()
    jump_origins = Set{Int}()
    for stmt in code.stmts
        if isa(stmt, GotoNode)
            push!(dest_blocks, stmt.label)
        elseif isa(stmt, GotoIfNot)
            push!(dest_blocks, stmt.dest)
        elseif isa(stmt, PhiNode)
            for edge in stmt.edges
                push!(jump_origins, edge)
            end
        end
    end
    block_start = Dict(first(code.cfg.blocks[x].stmts)=>x for x in dest_blocks)
    comefrom_labels = Set{Int}(last(code.cfg.blocks[x].stmts)+1 for x in jump_origins)
    block_terminators = Dict(last(block.stmts)=>i for (i,block) in pairs(code.cfg.blocks))
    function rename(val)
        if isa(val, SSAValue)
            if haskey(mapping, val.id)
                return SSAValue(mapping[val.id])
            end
        elseif isa(val, Argument)
            return SlotNumber(val.n)
        end
        return val
    end
    # Now translate the code
    new_code = Vector{Any}()
    label_mapping = Dict{Int, Int}()
    terminator_mapping = Dict{Int, Int}()
    fixup = Int[]
    for (idx, stmt) in pairs(code.stmts)
        if haskey(block_start, idx)
            push!(new_code, LabelNode(length(new_code) + 1))
            label_mapping[block_start[idx]] = length(new_code)
        elseif idx in comefrom_labels
            push!(new_code, LabelNode(length(new_code) + 1))
        end
        if isa(stmt, GotoIfNot)
            new_stmt = Expr(:gotoifnot, rename(stmt.cond), stmt.dest)
            push!(fixup, length(new_code)+1)
        elseif isa(stmt, ReturnNode)
            new_stmt = Expr(:return, rename(stmt.val))
        elseif isa(stmt, SSAValue)
            new_stmt = rename(stmt)
        elseif isa(stmt, PhiNode)
            new_stmt = ssaargmap(rename, stmt)
            push!(fixup, length(new_code)+1)
        elseif isa(stmt, GotoNode)
            push!(fixup, length(new_code)+1)
            new_stmt = stmt
        else
            new_stmt = ssaargmap(rename, stmt)
        end
        if haskey(mapping, idx)
            new_stmt = Expr(:(=), SSAValue(mapping[idx]), new_stmt)
        end
        if haskey(block_terminators, idx)
            terminator_mapping[block_terminators[idx]] = length(new_code)+1
        end
        push!(new_code, new_stmt)
    end
    for i in fixup
        val = new_code[i]
        if isexpr(val, :(=))
            val = val.args[2]
        end
        val = if isa(val, PhiNode)
            # Translate from BB edges to statement edges
            edges = map(val.edges) do edge
                terminator_mapping[edge]
            end
            PhiNode(convert(Vector{Any}, edges), val.values)
        elseif isa(val, GotoNode)
            GotoNode(label_mapping[val.label])
        elseif isexpr(val, :gotoifnot)
            Expr(:gotoifnot, val.args[1], label_mapping[val.args[2]])
        else
            @show val
            error()
        end
        if isexpr(new_code[i], :(=))
            new_code[i].args[2] = val
        else
            new_code[i] = val
        end
    end
    ci.code = new_code
    ci
end
