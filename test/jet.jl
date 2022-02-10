# JET Test
# ========
# check code quality of EA, especially, this test asserts that our main routine are free from (unnecessary) runtime dispatches

using Test, EscapeAnalysis, JET

function function_filter(@nospecialize(ft))
    ft === typeof(Core.Compiler.widenconst) && return false # `widenconst` is very untyped, ignore
    ft === typeof(EscapeAnalysis.escape_builtin!) && return false # `escape_builtin!` is very untyped, ignore
    return true
end

false && let
    target_modules = (EscapeAnalysis,)
    interp = EscapeAnalysis.EAUtils.EscapeAnalyzer(Core.Compiler.NativeInterpreter(), Tuple{}, true)
    get_escape_cache = EscapeAnalysis.EAUtils.get_escape_cache(interp)
    sig = Tuple{typeof(analyze_escapes), Core.Compiler.IRCode, Int, Bool, typeof(get_escape_cache)}
    test_opt(sig;
        function_filter,
        target_modules,
        # skip_nonconcrete_calls=false,
        )
    for m in methods(EscapeAnalysis.escape_builtin!)
        sig = m.sig
        Base._methods_by_ftype(sig, 1, Base.get_world_counter()) === false && continue
        types = collect(sig.parameters)
        types[2] = EscapeAnalysis.AnalysisState{typeof(get_escape_cache)}
        sig = Tuple{types...}
        test_opt(sig;
            function_filter,
            target_modules,
            # skip_nonconcrete_calls=false,
            )
    end
end
