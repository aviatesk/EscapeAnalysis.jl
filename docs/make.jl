using EscapeAnalysis, Documenter

let
    local README_PATH = normpath(@__DIR__, "src", "index.md")
    try
        s = let s = read(normpath(@__DIR__, "..", "README.md"), String)
            s = replace(s,
                "Core.Compiler.EscapeAnalysis." => "EscapeAnalysis.",
                "Base.code_escapes" => "EscapeAnalysis.EAUtils.code_escapes",
                "InteractiveUtils.@code_escapes" => "EscapeAnalysis.EAUtils.@code_escapes",
                )
            write(README_PATH, s)
        end
        makedocs(; modules = [EscapeAnalysis],
                   sitename = "EscapeAnalysis.jl",
                   pages = Any["EscapeAnalysis" => "index.md"],
                   format = Documenter.HTML(;
                       prettyurls = get(ENV, "CI", nothing) == "true",
                       ansicolor = true,
                   ),
                 )
    catch err
        rethrow(err)
    finally
        rm(README_PATH)
    end
end

deploydocs(; repo = "github.com/aviatesk/EscapeAnalysis.jl.git",
             push_preview = true,
             )
