const EA_AS_PKG = true
include(normpath(@__DIR__, "setup.jl"))
@testset "EscapeAnalysis" begin
    include(normpath(@__DIR__, "EscapeAnalysis.jl"))
end
