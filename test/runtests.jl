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
    phi = ir.stmts[3]
    @test isa(phi, NewOptimizer.PhiNode)
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
    # Maybe test some things here
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