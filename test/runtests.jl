using NewOptimizer
using Test
using Base.Meta

function undef_vars(x::Bool)
    if x
        a = 1
    end
    a
end

let ir = NewOptimizer.run_passes(undef_vars, Tuple{Bool})
    phi = first(filter(stmt->isa(stmt, NewOptimizer.PhiNode), ir.stmts))
    @test 1 == count(i->!isassigned(phi.values, i), 1:length(phi.values))
end

function loop()
    a = 1
    for i = 1:10
        a = i
    end
    a
end

let ir = NewOptimizer.run_passes(loop, Tuple{})
    # The first block is completely dead. Make
    # sure we maintain it nevertheless for CFG integrity
    @test length(ir.cfg.blocks) == 5
    @test length(ir.cfg.blocks[1].stmts) == 1
    @test ir.stmts[1] == nothing
end

# Test from base
struct A15259
    x
    y
end
# check that allocation was ellided
@eval f15259(x,y) = (a = $(Expr(:new, :A15259, :x, :y)); (a.x, a.y, getfield(a,1), getfield(a, 2)))
let ir = NewOptimizer.run_passes(f15259, Tuple{Any, Any})
    @test !any(expr->isexpr(expr, :new), ir.stmts)
end

# Motivating example (25663)
@noinline foo() = rand(Bool) ? 2 : nothing
@inline baz(x) = x ? (foo(), 1) : nothing
function bar(arg)
    x = baz(arg)
    x === nothing && return 0
    a, b = x
    a === nothing && return 1
    return a
end

let ir = NewOptimizer.run_passes(loop, Tuple{})
    @test !any(expr->NewOptimizer.is_call(expr, :tuple), ir.stmts)
end

struct Wrapper{T}
    x::T
end

@eval function foo(x::T) where {T}
    $(Expr(:new, Wrapper, :x)).x
end

let ir = NewOptimizer.run_passes(foo, Tuple{Any})
    @test !any(expr->NewOptimizer.is_call(expr, :getfield), ir.stmts)
end

using NewOptimizer
using NotInferenceDontLookHere

function bar()
    if rand(Bool)
        x = nothing
    else
        x = missing
    end
    x
end
@NI.code_typed bar()


function baz()
    if rand(Bool)
        x = 1
    else
    end
    x
end
@NI.code_typed baz()
baz()


function foo()
    if rand(Bool)
        x = 1
    else
    end
    @isdefined x
end
@NI.code_typed foo()
foo()

function funion(x,y)
    if y
       z = x[1] in (:isequal, :isapprox, :≈)
    else
       z = false
    end
    if z
       return 1
    else
       return 2
    end
end
@NI.code_typed funion(Any[:isequal], true)
funion(Any[:isequal], true)


function tuple_phi()
    x = (1, 1)
    while x[1] <= 10
        ccall(:jl_, Cvoid, (Any,), x[2])
        x = (1, x[2]+1)
    end
    x
end