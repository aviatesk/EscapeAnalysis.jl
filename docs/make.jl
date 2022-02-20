using EscapeAnalysis, Documenter

let
    local INDEX_PATH = normpath(@__DIR__, "src", "index.md")
    local s = read(INDEX_PATH, String)
    try
        let s = replace(s,
                "Core.Compiler.EscapeAnalysis." => "EscapeAnalysis.",
                """include(normpath(Sys.BINDIR, "..", "share", "julia", "test", "compiler", "EscapeAnalysis", "EAUtils.jl")); using .EAUtils""" => "using EscapeAnalysis",
                )
            write(INDEX_PATH, s)
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
        write(INDEX_PATH, s)
    end
end

deploydocs(; repo = "github.com/aviatesk/EscapeAnalysis.jl.git",
             push_preview = true,
             )
