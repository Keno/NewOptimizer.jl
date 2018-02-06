#############
# from Base #
#############

# essential files and libraries
include("essentials.jl")
include("ctypes.jl")
include("generator.jl")
include("reflection.jl")
include("options.jl")

# core operations & types
function return_type end # promotion.jl expects this to exist
include("promotion.jl")
include("tuple.jl")
include("pair.jl")
include("traits.jl")
include("range.jl")
include("expr.jl")
include("error.jl")

# core numeric operations & types
include("bool.jl")
include("number.jl")
include("int.jl")
include("operators.jl")
include("pointer.jl")
const checked_add = +
const checked_sub = -

# core array operations
include("indices.jl")
include("array.jl")
include("abstractarray.jl")

# map-reduce operators
macro simd(forloop)
    esc(forloop)
end
include("reduce.jl")

# core structures
include("bitarray.jl")
include("bitset.jl")
include("abstractdict.jl")
include("iterators.jl")
include("namedtuple.jl")

# core docsystem
include("docs/core.jl")

############
# compiler #
############

inlining_enabled() = (JLOptions().can_inline == 1)
coverage_enabled() = (JLOptions().code_coverage != 0)

include("compiler/utilities.jl")
include("compiler/validation.jl")

include("compiler/inferenceresult.jl")
include("compiler/params.jl")
include("compiler/inferencestate.jl")

include("compiler/typeutils.jl")
include("compiler/typelimits.jl")
include("compiler/typelattice.jl")
include("compiler/tfuncs.jl")

include("compiler/abstractinterpretation.jl")
include("compiler/typeinfer.jl")
include("compiler/optimize.jl") # TODO: break this up further + extract utilities

# Intentionally don't call bootstrap.jl here