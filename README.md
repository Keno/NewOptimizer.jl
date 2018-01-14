# NotInferenceDontLookHere

This is not inference. However, it does help you with developing inference
by loading a separate copy of inference into this package and hooking up
Revise. This allows you to easily test changes to inference in isolation.

# Usage
```julia
using NotInferenceDontLookHere
# For convenience, `NI` is introduced as a short alias

# Infer something
f(x) = x
@NI.code_typed f(1)
```
