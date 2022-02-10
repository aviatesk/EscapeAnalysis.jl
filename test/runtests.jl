using Test

@testset "EscapeAnalysis" begin
    @testset "Local EA" begin
        include(normpath(@__DIR__, "local.jl"))
    end
    
    @testset "IPO EA" begin
        include(normpath(@__DIR__, "interprocedural.jl"))
    end

    @testset "JET Test" begin
        include(normpath(@__DIR__, "jet.jl"))
    end
end
