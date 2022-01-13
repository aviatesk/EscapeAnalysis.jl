using EscapeAnalysis, Documenter

let
    local README = normpath(@__DIR__, "src", "index.md")
    try
        cp(normpath(@__DIR__, "..", "README.md"), README)
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
        rm(README)
    end
end

deploydocs(; repo = "github.com/aviatesk/EscapeAnalysis.jl.git",
             push_preview = true,
             )
