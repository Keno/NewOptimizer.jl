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
include("refvalue.jl")

# checked arithmetic
const checked_add = +
const checked_sub = -
const SignedInt = Union{Int8,Int16,Int32,Int64,Int128}
const UnsignedInt = Union{UInt8,UInt16,UInt32,UInt64,UInt128}
sub_with_overflow(x::T, y::T) where {T<:SignedInt}   = checked_ssub_int(x, y)
sub_with_overflow(x::T, y::T) where {T<:UnsignedInt} = checked_usub_int(x, y)
sub_with_overflow(x::Bool, y::Bool) = (x-y, false)
add_with_overflow(x::T, y::T) where {T<:SignedInt}   = checked_sadd_int(x, y)
add_with_overflow(x::T, y::T) where {T<:UnsignedInt} = checked_uadd_int(x, y)
add_with_overflow(x::Bool, y::Bool) = (x+y, false)

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
include("abstractset.jl")
include("iterators.jl")
using .Iterators: zip, enumerate
using .Iterators: Flatten, product  # for generators
include("namedtuple.jl")

# core docsystem
include("docs/core.jl")

# SubArray
include("subarray.jl")
macro views(x); esc(x); end

# sorting
function sort end
function sort! end
function issorted end
function sortperm end
include("ordering.jl")
using .Order
include("sort.jl")
using .Sort

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

