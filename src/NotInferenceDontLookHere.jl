__precompile__(false)
baremodule NotInferenceDontLookHere

using Core.Intrinsics
import Core: print, println, show, write, unsafe_write, STDOUT, STDERR

ccall(:jl_set_istopmod, Void, (Any, Bool), NotInferenceDontLookHere, false)

eval(x) = Core.eval(NotInferenceDontLookHere, x)
eval(m, x) = Core.eval(m, x)

include(x) = Core.include(NotInferenceDontLookHere,
    Core.Main.Base.joinpath(Core.Main.Base.JULIA_HOME, Core.Main.Base.DATAROOTDIR, "julia", "base", x))
include(mod, x) = Core.include(mod, x)

function return_type end

base(x) = joinpath()

Core.include(NotInferenceDontLookHere, Core.Main.Base.joinpath(
    Core.Main.Base.dirname(Core.Main.Base.@__FILE__), "coreimg2.jl"))

end # module

# Auto-track this with Revise
module ReviseTrack
    using Revise
    using NotInferenceDontLookHere

    function __init__()
        push!(Revise.dont_watch_pkgs, :NotInferenceDontLookHere)
        push!(Revise.silence_pkgs, :NotInferenceDontLookHere)
        push!(Revise.dont_watch_pkgs, :ReviseTrack)
        push!(Revise.silence_pkgs, :ReviseTrack)
        empty!(Revise.new_files)
        Revise.parse_source(joinpath(dirname(@__FILE__),"coreimg2.jl"), NotInferenceDontLookHere, joinpath(JULIA_HOME,
            Base.DATAROOTDIR, "julia", "base"))
        Revise.process_parsed_files(Revise.new_files)
    end
end
