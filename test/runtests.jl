using NewOptimizer
using Test

function undef_vars(x::Bool)
    if x
        a = 1
    end
    a
end

let ir = NewOptimizer.run_passes(undef_vars, Tuple{Bool})
    phi = ir.smts[3]
    @test isa(phi, NewOptimizer.PhiNode)
    @test 1 == count(i->!isassigned(phi.values, i), 1:length(phi.values))
end