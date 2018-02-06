__precompile__(false)
baremodule NotInferenceDontLookHere

function code_llvm end

using Core.Intrinsics
using Core.Intrinsics
using NewOptimizer
using InteractiveUtils

import Core: print, println, show, write, unsafe_write, STDOUT, STDERR,
             _apply, svec, apply_type, Builtin, IntrinsicFunction, MethodInstance

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
    params = Params(world)
    for x in Core.Main.Base._methods(f, types, -1, world)
        meth = Core.Main.Base.func_for_method_checked(x[3], types)
        (_, code, ty) = typeinf_code(meth, x[1], x[2], optimize, optimize, params)
        code === nothing && error("inference not successful") # Inference disabled?
        push!(asts, uncompressed_ast(meth, code) => ty)
    end
    return asts
end

# Twiddle slotfalgs for our purposes - Adapted from Cassette
function twiddle_code_info!(code_info, fT, argsT)
    code_info.slotnames = Any[code_info.slotnames[1], :f, :args, code_info.slotnames[2:end]...]
    code_info.slottypes = Any[code_info.slottypes[1], fT, argsT, code_info.slottypes[2:end]...]
    code_info.slotflags = Any[code_info.slotflags[1], 0x00, 0x00, code_info.slotflags[2:end]...]
    Cassette.replace_match!(x -> isa(x, SlotNumber) || isa(x, NewvarNode) || isa(x, TypedSlot), code_info.code) do x
        if isa(x, NewvarNode) && x.slot.id > 1
            return NewvarNode(SlotNumber(x.slot.id + 2))
        elseif isa(x, TypedSlot) && x.id > 1
            return TypedSlot(x.id + 2, x.typ)
        elseif x.id > 1
            return SlotNumber(x.id + 2)
        end
        return x
    end
end

function expand_varargs!(code_info, argTs)
    new_code = Cassette.copy_prelude_code(code_info.code)
    prelude_end = length(new_code)
    nargs = length(argTs)
    for i in 1:nargs
        slot = i + 3
        actual_argument = Expr(:call, GlobalRef(Core, :getfield), SlotNumber(3), i)
        actual_argument.typ = argTs[i]
        push!(new_code, :($(SlotNumber(slot)) = $actual_argument))
        code_info.slotflags[slot] |= 0x01 << 0x01 # make sure the "assigned" bitflag is set
    end
    append!(new_code, code_info.code[(prelude_end + 1):end])
    code_info.code = Cassette.fix_labels_and_gotos!(new_code)
end

function code_llvm2(@nospecialize(f), @nospecialize(types=Tuple), args...)
    eval(quote
        @generated function code_llvm_helper(f, args...)
            CI = code_typed(f.parameters[1], Tuple{args...})[1].first
            twiddle_code_info!(CI, f, Tuple{args...})
            expand_varargs!(CI, args)
            return CI
        end
        Base.code_llvm(code_llvm_helper, Tuple{Val{$f}, $(types.parameters...)})
    end)
end

for fname in [:code_typed, :code_lowered]
    @Base.eval begin
        macro ($fname)(ex0)
            thecall = InteractiveUtils.gen_call_with_extracted_types(__module__, $(Expr(:quote, fname)), ex0)
            quote
                results = $thecall
                length(results) == 1 ? results[1] : results
            end
        end
    end
end

end # module
