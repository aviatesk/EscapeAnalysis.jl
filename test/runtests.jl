using EscapeAnalysis, InteractiveUtils, Test
import EscapeAnalysis:
    EscapeInformation
for t in subtypes(EscapeInformation)
    canonicalname = Symbol(parentmodule(t), '.', nameof(t))
    canonicalpath = Symbol.(split(string(canonicalname), '.'))

    modpath = Expr(:., canonicalpath[1:end-1]...)
    symname = Expr(:., last(canonicalpath))
    ex = Expr(:import, Expr(:(:), modpath, symname))
    Core.eval(@__MODULE__, ex)
end

@testset "EscapeAnalysis" begin

let # simplest
    src, escapes = analyze_escapes((Any,)) do a # no escape
        return nothing
    end
    @test escapes.arguments[2] isa NoEscape
end

let # global assignement
    src, escapes = analyze_escapes((Any,)) do a
        global aa = a
        return nothing
    end
    @test escapes.arguments[2] isa Escape
end

let # return
    src, escapes = analyze_escapes((Any,)) do a
        return a
    end
    @test escapes.arguments[2] isa ReturnEscape
end

@testset "control flows" begin
    let # branching
        src, escapes = analyze_escapes((Any,Bool,)) do a, c
            if c
                return nothing # a doesn't escape in this branch
            else
                return a # a escapes to a caller
            end
        end
        @test escapes.arguments[2] isa ReturnEscape
    end

    let # exception
        src, escapes = analyze_escapes((Any,)) do a
            try
                nothing
            catch err
                return a # return escape
            end
        end
        @test escapes.arguments[2] isa ReturnEscape
    end
end

mutable struct Condition
    condition::Bool
end

let # more complex
    src, escapes = analyze_escapes((Bool,)) do c
        x = Vector{Condition}() # escape
        y = Condition(c) # escape
        if c
            push!(x, y) # escape
            return nothing
        else
            return x # return escape
        end
    end

    i = findfirst(==(Vector{Condition}), src.stmts.type)
    @assert !isnothing(i)
    @test escapes.ssavalues[i] isa Escape
    i = findfirst(==(Condition), src.stmts.type)
    @assert !isnothing(i)
    @test escapes.ssavalues[i] isa Escape
end

let # simple allocation
    src, escapes = analyze_escapes((Bool,)) do c
        cond = Condition(c) # just allocated, never escapes
        return cond.condition ? nothing : 1
    end

    i = findfirst(==(Condition), src.stmts.type) # allocation statement
    @assert !isnothing(i)
    @test escapes.ssavalues[i] isa NoEscape
end

@testset "inter-procedural" begin
    m = Module()

    @eval m @noinline f_noescape(x) = (broadcast(identity, x); nothing)
    let
        src, escapes = @eval m $analyze_escapes() do
            f_noescape(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), src.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test escapes.ssavalues[i] isa NoEscape
    end

    @eval m @noinline f_returnescape(x) = broadcast(identity, x)
    let
        src, escapes = @eval m $analyze_escapes() do
            f_returnescape(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), src.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test escapes.ssavalues[i] isa ReturnEscape
    end

    @eval m @noinline f_escape(x) = (global xx = x) # obvious escape
    let
        src, escapes = @eval m $analyze_escapes() do
            f_escape(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), src.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test escapes.ssavalues[i] isa Escape
    end
end

end # @testset "EscapeAnalysis" begin