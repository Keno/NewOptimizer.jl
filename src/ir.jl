"""
Like UnitRange{Int}, but can handle the `last` field, being temporarily
< first (this can happen during compacting)
"""
struct StmtRange <: Base.AbstractUnitRange{Int}
    first::Int
    last::Int
end
Base.first(r::StmtRange) = r.first
Base.last(r::StmtRange) = r.last
Base.start(r::StmtRange) = 0
Base.done(r::StmtRange, state) = r.last - r.first < state
Base.next(r::StmtRange, state) = (r.first + state, state + 1)

struct BasicBlock
    stmts::StmtRange
    preds::Vector{Int}
    succs::Vector{Int}
end
function BasicBlock(stmts::StmtRange)
    BasicBlock(stmts, Int[], Int[])
end
function BasicBlock(old_bb, stmts)
    BasicBlock(stmts, old_bb.preds, old_bb.succs)
end

struct CFG
    blocks::Vector{BasicBlock}
    index::Vector{Int}
end


struct IRCode
    stmts::Vector{Any}
    types::Vector{Any}
    cfg::CFG
    new_nodes::Vector{Tuple{Int, Type, Any}}
    mod::Module
end
IRCode(stmts, cfg, mod) = IRCode(stmts, Any[], cfg, Tuple{Int, Type, Any}[], mod)

struct OldSSAValue
    id::Int
end

struct NewSSAValue
    id::Int
end

mutable struct UseRefIterator{T}
    stmt::T
end
Base.getindex(it::UseRefIterator) = it.stmt

struct UseRef
    urs::UseRefIterator
    use::Int
end

struct OOBToken
end

struct UndefToken
end

function Base.getindex(x::UseRef)
    stmt = x.urs.stmt
    if isexpr(stmt, :call) || isexpr(stmt, :invoke) || isexpr(stmt, :new) ||
       isexpr(stmt, :gc_preserve_begin) || isexpr(stmt, :gc_preserve_end) || isexpr(stmt, :foreigncall)
        x.use > length(stmt.args) && return OOBToken()
        stmt.args[x.use]
    elseif isa(stmt, GotoIfNot)
        x.use == 1 || return OOBToken()
        return stmt.cond
    elseif isa(stmt, ReturnNode) || isa(stmt, PiNode)
        x.use == 1 || return OOBToken()
        return stmt.val
    elseif isa(stmt, PhiNode)
        x.use > length(stmt.values) && return OOBToken()
        isassigned(stmt.values, x.use) || return UndefToken()
        return stmt.values[x.use]
    else
        return OOBToken()
    end
end

function Base.setindex!(x::UseRef, v)
    stmt = x.urs.stmt
    if isexpr(stmt, :call) || isexpr(stmt, :invoke) ||
       isexpr(stmt, :new) || isexpr(stmt, :gc_preserve_begin) || isexpr(stmt, :gc_preserve_end) ||
       isexpr(stmt, :foreigncall)
        x.use > length(stmt.args) && throw(BoundsError())
        stmt.args[x.use] = v
    elseif isa(stmt, GotoIfNot)
        x.use == 1 || throw(BoundsError())
        x.urs.stmt = GotoIfNot{Any}(v, stmt.dest)
    elseif isa(stmt, ReturnNode)
        x.use == 1 || throw(BoundsError())
        x.urs.stmt = typeof(stmt)(v)
    elseif isa(stmt, PiNode)
        x.use == 1 || throw(BoundsError())
        x.urs.stmt = typeof(stmt)(v, stmt.typ)
    elseif isa(stmt, PhiNode)
        x.use > length(stmt.values) && throw(BoundsError())
        isassigned(stmt.values, x.use) || throw(BoundsError())
        stmt.values[x.use] = v
    else
        return OOBToken()
    end
end

userefs(x) = UseRefIterator(x)

Base.start(it::UseRefIterator) = 1
function Base.next(it::UseRefIterator, use)
    x = UseRef(it, use)
    v = x[]
    v === UndefToken() && return next(it, use + 1)
    x, use + 1
end
function Base.done(it::UseRefIterator, use)
    x, _ = next(it, use)
    v = x[]
    v === OOBToken() && return true
    false
end

function scan_ssa_use!(used, stmt)
    if isa(stmt, SSAValue)
        push!(used, stmt.id)
    end
    for useref in userefs(stmt)
        val = useref[]
        if isa(val, SSAValue)
            push!(used, val.id)
        end
    end
end

function ssamap(f, stmt)
    urs = userefs(stmt)
    for op in urs
        val = op[]
        if isa(val, SSAValue)
            op[] = f(val)
        end
    end
    urs[]
end


function print_node(io::IO, idx, stmt, used, maxsize; color = true, print_typ=true)
    if idx in used
        pad = " "^(maxsize-length(string(idx)))
        print(io, "%$idx $pad= ")
    else
        print(io, " "^(maxsize+4))
    end
    if isa(stmt, PhiNode)
        args = map(1:length(stmt.edges)) do i
            e = stmt.edges[i]
            v = !isassigned(stmt.values, i) ? "#undef" :
                sprint() do io′
                    print_ssa(io′, stmt.values[i])
                end
            "$e => $v"
        end
        print(io, "φ ", '(', join(args, ", "), ')')
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
        if print_typ && stmt.typ !== Any
            print(io, "::$(stmt.typ)")
        end
    elseif isexpr(stmt, :new)
        print(io, "new(")
        print(io, join(map(arg->sprint(io->print_ssa(io, arg)), stmt.args), ", "))
        print(io, ")")
    else
        print(io, stmt)
    end
end

print_ssa(io::IO, val) = isa(val, SSAValue) ? print(io, "%$(val.id)") : print(io, val)
function Base.show(io::IO, code::IRCode)
    used = Set{Int}()
    println(io, "Code")
    foreach(stmt->scan_ssa_use!(used, stmt), code.stmts)
    foreach(((_a,_b,node),)->scan_ssa_use!(used, node), code.new_nodes)
    if isempty(used)
        maxsize = 0
    else
        maxused = maximum(used)
        maxsize = length(string(maxused))
    end
    cfg = code.cfg
    max_bb_idx_size = length(string(length(cfg.blocks)))
    bb_idx = 1
    perm = sortperm(code.new_nodes, by = x->x[1])
    new_nodes_perm = Iterators.Stateful(perm)
    for (idx, stmt) in enumerate(code.stmts)
        bbrange = cfg.blocks[bb_idx].stmts
        bb_pad = max_bb_idx_size - length(string(bb_idx))
        if idx != last(bbrange)
            if idx == first(bbrange)
                print(io, "$(bb_idx) ","─"^(1+bb_pad)," ")
            else
                print(io, "│  "," "^max_bb_idx_size)
            end
        end
        print_sep = false
        if idx == last(bbrange)
            print_sep = true
        end
        floop = true
        while !isempty(new_nodes_perm) && code.new_nodes[Base.peek(new_nodes_perm)][1] == idx
            node_idx = popfirst!(new_nodes_perm)
            _, typ, node = code.new_nodes[node_idx]
            node_idx += length(code.stmts)
            if print_sep
                if floop
                    print(io, "$(bb_idx) ","─"^(1+bb_pad)," ")
                else
                    print(io, "│  "," "^max_bb_idx_size)
                end
            end
            print_sep = true
            floop = false
            print_ssa_typ = !isa(node, PiNode) && node_idx in used
            Base.with_output_color(:yellow, io) do io′
                print_node(io′, node_idx, node, used, maxsize; color = false,
                    print_typ=!print_ssa_typ || (isa(node, Expr) && typ != node.typ))
            end
            if print_ssa_typ
                printstyled(io, "::$(typ)", color=:red)
            end
            println(io)
        end
        if print_sep
            if idx == first(bbrange) && floop
                print(io, "$(bb_idx) ","─"^(1+bb_pad)," ")
            else
                print(io, idx == last(bbrange) ? string("└", "─"^(1+max_bb_idx_size), " ") :
                    string("│  ", " "^max_bb_idx_size))
            end
        end
        if idx == last(bbrange)
            bb_idx += 1
        end
        typ = code.types[idx]
        print_ssa_typ = !isa(stmt, PiNode) && idx in used
        print_node(io, idx, stmt, used, maxsize,
            print_typ=!print_ssa_typ || (isa(stmt, Expr) && typ != stmt.typ))
        if print_ssa_typ
            printstyled(io, "::$(typ)", color=:red)
        end
        println(io)
    end
end

mutable struct IncrementalCompact
    ir::IRCode
    result::Vector{Any}
    result_types::Vector{Any}
    ssa_rename::Vector{Any}
    used_ssas::Vector{Int}
    late_fixup::Vector{Int}
    keep_meta::Bool
    new_nodes_perm::Any
    idx::Int
    result_idx::Int
    function IncrementalCompact(code::IRCode; keep_meta = false)
        new_nodes_perm = Iterators.Stateful(sortperm(code.new_nodes, by=x->x[1]))
        result = Array{Any}(uninitialized, length(code.stmts) + length(code.new_nodes))
        result_types = Array{Any}(uninitialized, length(code.stmts) + length(code.new_nodes))
        ssa_rename = Any[SSAValue(i) for i = 1:(length(code.stmts) + length(code.new_nodes))]
        late_fixup = Vector{Int}()
        used_ssas = fill(0, length(code.stmts) + length(code.new_nodes))
        new(code, result, result_types, ssa_rename, used_ssas, late_fixup, keep_meta, new_nodes_perm, 1, 1)
    end
end

struct TypesView
    compact::IncrementalCompact
end
types(compact::IncrementalCompact) = TypesView(compact)

function Base.getindex(compact::IncrementalCompact, idx)
    if idx < compact.result_idx
        return compact.result[idx]
    else
        return compact.ir.stmts[idx]
    end
end

function Base.setindex!(compact::IncrementalCompact, v, idx)
    if idx < compact.result_idx
        # Kill count for current uses
        for ops in userefs(compact.result[idx])
            val = ops[]
            isa(val, SSAValue) && (compact.used_ssas[val.id] -= 1)
        end
        # Add count for new use
        isa(v, SSAValue) && (compact.used_ssas[v.id] += 1)
        return compact.result[idx] = v
    else
        return compact.ir.stmts[idx] = v
    end
end

function Base.getindex(view::TypesView, idx)
    if idx < view.compact.result_idx
        return view.compact.result_types[idx]
    else
        return view.compact.ir.types[idx]
    end
end

function value_typ(ir::IRCode, value)
    isa(value, SSAValue) && return ir.types[value.id]
    isa(value, GlobalRef) && return typeof(getfield(value.mod, value.name))
    return typeof(value)
end

function value_typ(ir::IncrementalCompact, value)
    isa(value, SSAValue) && return types(ir)[value.id]
    isa(value, GlobalRef) && return typeof(getfield(value.mod, value.name))
    return typeof(value)
end


Base.start(compact::IncrementalCompact) = (1,1,1)
function Base.done(compact::IncrementalCompact, (idx, _a, _b)::Tuple{Int, Int, Int})
    return idx > length(compact.ir.stmts) && isempty(compact.new_nodes_perm)
end

function process_node!(result, result_idx, ssa_rename, late_fixup, used_ssas, stmt, idx, processed_idx, keep_meta)
    ssa_rename[idx] = SSAValue(result_idx)
    if stmt === nothing
        # eliminate this node
    elseif !keep_meta && (isexpr(stmt, :meta) || isa(stmt, LineNumberNode))
        # eliminate this node
    elseif isa(stmt, GotoNode)
        result[result_idx] = stmt
        result_idx += 1
    elseif isexpr(stmt, :call) || isexpr(stmt, :invoke) || isa(stmt, ReturnNode) || isexpr(stmt, :gc_preserve_begin) ||
           isexpr(stmt, :gc_preserve_end) || isexpr(stmt, :foreigncall)
        result[result_idx] = renumber_ssa!(stmt, ssa_rename, true, used_ssas)
        result_idx += 1
    elseif isa(stmt, PhiNode)
        values = Vector{Any}(uninitialized, length(stmt.values))
        for i = 1:length(stmt.values)
            isassigned(stmt.values, i) || continue
            val = stmt.values[i]
            if isa(val, SSAValue)
                if val.id > processed_idx
                    push!(late_fixup, result_idx)
                    val = OldSSAValue(val.id)
                else
                    val = renumber_ssa!(val, ssa_rename, true, used_ssas)
                end
            end
            values[i] = val
        end
        result[result_idx] = PhiNode(stmt.edges, values)
        result_idx += 1
    elseif isa(stmt, SSAValue) || (!isa(stmt, Expr) && !isa(stmt, PhiNode) && !isa(stmt, PiNode) && !isa(stmt, GotoIfNot))
        # Constant or identity assign, replace uses of this
        # ssa value with its result
        stmt = isa(stmt, SSAValue) ? ssa_rename[stmt.id] : stmt
        ssa_rename[idx] = stmt
    else
        result[result_idx] = renumber_ssa!(stmt, ssa_rename, true, used_ssas)
        result_idx += 1
    end
    return result_idx
end
function process_node!(compact::IncrementalCompact, result_idx, stmt, idx, processed_idx)
    process_node!(compact.result, result_idx, compact.ssa_rename,
        compact.late_fixup, compact.used_ssas, stmt, idx, processed_idx, compact.keep_meta)
end

function Base.next(compact::IncrementalCompact, (idx, active_bb, old_result_idx)::Tuple{Int, Int, Int})
    if length(compact.result) < old_result_idx
        resize!(compact.result, old_result_idx)
        resize!(compact.result_types, old_result_idx)
    end
    bb = compact.ir.cfg.blocks[active_bb]
    if !isempty(compact.new_nodes_perm) && compact.ir.new_nodes[Base.peek(compact.new_nodes_perm)][1] == idx
        new_idx = popfirst!(compact.new_nodes_perm)
        _, typ, new_node = compact.ir.new_nodes[new_idx]
        new_idx += length(compact.ir.stmts)
        compact.result_types[old_result_idx] = typ
        result_idx = process_node!(compact, old_result_idx, new_node, new_idx, idx)
        (old_result_idx == result_idx) && return next(compact, (idx, result_idx))
        compact.result_idx = result_idx
        return (old_result_idx, compact.result[old_result_idx]), (compact.idx, active_bb, compact.result_idx)
    end
    # This will get overwritten in future iterations if
    # result_idx is not, incremented, but that's ok and expected
    compact.result_types[old_result_idx] = compact.ir.types[idx]
    result_idx = process_node!(compact, old_result_idx, compact.ir.stmts[idx], idx, idx)
    if idx == last(bb.stmts)
        # If this was the last statement in the BB and we decided to skip it, insert a
        # dummy `nothing` node, to prevent changing the structure of the CFG
        if result_idx == first(bb.stmts)
            compact.result[old_result_idx] = nothing
            result_idx = old_result_idx + 1
        end
        compact.ir.cfg.blocks[active_bb] = BasicBlock(bb, StmtRange(first(bb.stmts), result_idx-1))
        active_bb += 1
        if active_bb <= length(compact.ir.cfg.blocks)
            new_bb = compact.ir.cfg.blocks[active_bb]
            compact.ir.cfg.blocks[active_bb] = BasicBlock(new_bb,
                StmtRange(result_idx, last(new_bb.stmts)))
        end
    end
    (old_result_idx == result_idx) && return next(compact, (idx + 1, active_bb, result_idx))
    compact.idx = idx + 1
    compact.result_idx = result_idx
    return (old_result_idx, compact.result[old_result_idx]), (compact.idx, active_bb, compact.result_idx)
end

function maybe_erase_unused!(extra_worklist, compact, idx)
   if stmt_effect_free(compact.result[idx], compact.ir, compact.ir.mod)
        for ops in userefs(compact.result[idx])
            val = ops[]
            if isa(val, SSAValue)
                if compact.used_ssas[val.id] == 1
                    if val.id < idx
                        push!(extra_worklist, val.id)
                    end
                end
                compact.used_ssas[val.id] -= 1
            end
        end
        compact.result[idx] = nothing
    end
end

function finish(compact::IncrementalCompact)
    for idx in compact.late_fixup
        stmt = compact.result[idx]
        @assert isa(stmt, PhiNode)
        values = Vector{Any}(uninitialized, length(stmt.values))
        for i = 1:length(stmt.values)
            isassigned(stmt.values, i) || continue
            val = stmt.values[i]
            if isa(val, OldSSAValue)
                val = compact.ssa_rename[val.id]
                if isa(val, SSAValue)
                    compact.used_ssas[val.id] += 1
                end
            end
            values[i] = val
        end
        compact.result[idx] = PhiNode(stmt.edges, values)
    end
    # Record this somewhere?
    result_idx = compact.result_idx
    resize!(compact.result, result_idx-1)
    resize!(compact.result_types, result_idx-1)
    bb = compact.ir.cfg.blocks[end]
    compact.ir.cfg.blocks[end] = BasicBlock(bb,
                StmtRange(first(bb.stmts), result_idx-1))
    # Perform simple DCE for unused values
    extra_worklist = Int[]
    for (idx, nused) in enumerate(compact.used_ssas)
        idx >= result_idx && break
        nused == 0 || continue
        maybe_erase_unused!(extra_worklist, compact, idx)
    end
    while !isempty(extra_worklist)
        maybe_erase_unused!(extra_worklist, compact, pop!(extra_worklist))
    end
    IRCode(compact.result, compact.result_types, compact.ir.cfg, Any[], compact.ir.mod)
end

function compact!(code::IRCode)
    compact = IncrementalCompact(code)
    # Just run through the iterator without any processing
    foreach(_->nothing, compact)
    return finish(compact)
end
