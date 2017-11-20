# NotInferenceDontLookHere

This is not inference. However, it does help you with developing inference
by loading a separate copy of inference into this package and hooking up
Revise. This allows you to easily test changes to inference in isolation.

# Usage
```julia
using NotInferenceDontLookHere
# For convenience, can use a shorted name
const NI = NotInferenceDontLookHere

# Infer something
f(x) = x
mi = NI.code_for_method(first(methods(f)), Tuple{typeof(f), Int64}, Core.svec(), typemax(UInt))
NI.typeinf_ext(method_instance, typemax(UInt))
```
