module NewOptimizer

include("ir.jl")
include("domtree.jl")
include("passes.jl")
include("slot2ssa.jl")
include("new_ir.jl")
include("legacy.jl")
include("queries.jl")
include("verify.jl")

end # module
