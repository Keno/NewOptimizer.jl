## Load essential files and libraries
include("essentials.jl")
include("ctypes.jl")
include("generator.jl")
include("reflection.jl")
include("options.jl")

# core operations & types
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

## core structures
include("bitarray.jl")
include("bitset.jl")
include("associative.jl")

# core docsystem
include("docs/core.jl")

# compiler
include("codevalidation.jl")
include("inference.jl")
