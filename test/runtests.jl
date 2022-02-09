using Test

@testset "EscapeAnalysis" begin
    include(normpath(@__DIR__, "EscapeAnalysis.jl"))
end
