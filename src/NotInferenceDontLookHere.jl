__precompile__(false)
baremodule NotInferenceDontLookHere

using Core.Intrinsics
import Core: print, println, show, write, unsafe_write, STDOUT, STDERR

const NI = NotInferenceDontLookHere
export NI

const Base = Core.Main.Base

const getproperty = getfield
const setproperty! = setfield!

ccall(:jl_set_istopmod, Cvoid, (Any, Bool), NotInferenceDontLookHere, false)

eval(x) = Core.eval(NotInferenceDontLookHere, x)
eval(m, x) = Core.eval(m, x)

include(x) = include(NotInferenceDontLookHere,
    Base.joinpath(Base.Sys.BINDIR, Base.DATAROOTDIR, "julia", "base", x))
function include(mod, path)
    Base.foreach(Base.include_callbacks) do callback # to preserve order, must come before Core.include
        Base.invokelatest(callback, mod, path)
    end
    Core.include(mod, path)
end

function return_type end

base(x) = joinpath()

include(NotInferenceDontLookHere, Core.Main.Base.joinpath(
    Core.Main.Base.dirname(Core.Main.Base.@__FILE__), "coreimg2.jl"))

function code_typed(@nospecialize(f), @nospecialize(types=Tuple), optimize=true)
    types = Core.Main.Base.to_tuple_type(types)
    asts = []
    world = ccall(:jl_get_world_counter, UInt, ())
    params = InferenceParams(world)
    for x in Core.Main.Base._methods(f, types, -1, world)
        meth = Core.Main.Base.func_for_method_checked(x[3], types)
        (_, code, ty) = typeinf_code(meth, x[1], x[2], optimize, optimize, params)
        code === nothing && error("inference not successful") # Inference disabled?
        push!(asts, uncompressed_ast(meth, code) => ty)
    end
    return asts
end

macro code_typed(ex0)
    thecall = Core.Main.Base.gen_call_with_extracted_types(__module__, code_typed, ex0)
    quote
        results = $thecall
        length(results) == 1 ? results[1] : results
    end
end

end # module
