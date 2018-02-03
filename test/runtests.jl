using NewOptimizer
using Test

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