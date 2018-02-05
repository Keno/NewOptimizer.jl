function NotInferenceDontLookHere.abstract_eval_ssavalue(s::SSAValue, src::IRCode)
    src.types[s.id]
end