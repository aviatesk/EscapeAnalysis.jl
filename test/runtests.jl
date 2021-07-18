using EscapeAnalysis, InteractiveUtils, Test, JETTest

@testset "EscapeAnalysis" begin

mutable struct MutableSome{T}
    value::T
end

@testset "basics" begin
    let # simplest
        src, escapes = analyze_escapes((Any,)) do a # return to caller
            return nothing
        end
        @test is_return_escape(escapes.arguments[2])
    end

    let # global assignement
        src, escapes = analyze_escapes((Any,)) do a
            global aa = a
            return nothing
        end
        @test is_escape(escapes.arguments[2])
    end

    let # return
        src, escapes = analyze_escapes((Any,)) do a
            return a
        end
        @test is_return_escape(escapes.arguments[2])
    end

    # https://github.com/aviatesk/EscapeAnalysis.jl/pull/16
    let # don't propagate escape information for bitypes
        src, escapes = analyze_escapes((Nothing,)) do a
            global bb = a
        end
        @test is_return_escape(escapes.arguments[2])
    end
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
        @test is_return_escape(escapes.arguments[2])
    end

    let # π node
        src, escapes = analyze_escapes((Any,)) do a
            if isa(a, Regex)
                identity(a) # compiler will introduce π node here
                return a    # escape !
            else
                return nothing
            end
        end
        @test is_return_escape(escapes.arguments[2])
    end

    let # loop
        src, escapes = analyze_escapes((Int, Regex,)) do n, r
            rs = Regex[]
            while n > 0
                push!(rs, r)
                n -= 1
            end
            return rs
        end
        @test is_escape(escapes.arguments[3])
    end

    let # exception
        src, escapes = analyze_escapes((Any,)) do a
            try
                nothing
            catch err
                return a # return escape
            end
        end
        @test is_return_escape(escapes.arguments[2])
    end
end

mutable struct MyMutable
    cond::Bool
end

let # more complex
    src, escapes = analyze_escapes((Bool,)) do c
        x = Vector{MyMutable}() # escape
        y = MyMutable(c) # escape
        if c
            push!(x, y) # escape
            return nothing
        else
            return x # return escape
        end
    end

    i = findfirst(==(Vector{MyMutable}), src.stmts.type)
    @assert !isnothing(i)
    @test is_escape(escapes.ssavalues[i])
    i = findfirst(==(MyMutable), src.stmts.type)
    @assert !isnothing(i)
    @test is_escape(escapes.ssavalues[i])
end

let # simple allocation
    src, escapes = analyze_escapes((Bool,)) do c
        mm = MyMutable(c) # just allocated, never escapes
        return mm.cond ? nothing : 1
    end

    i = findfirst(==(MyMutable), src.stmts.type) # allocation statement
    @assert !isnothing(i)
    @test is_no_escape(escapes.ssavalues[i])
end

@testset "inter-procedural" begin
    m = Module()

    # FIXME currently we can't prove the effect-freeness of `getfield(RefValue{String}, :x)`
    # because of this check https://github.com/JuliaLang/julia/blob/94b9d66b10e8e3ebdb268e4be5f7e1f43079ad4e/base/compiler/tfuncs.jl#L745
    # and thus it leads to the following two broken tests

    @eval m @noinline f_noescape(x) = (broadcast(identity, x); nothing)
    let
        src, escapes = @eval m $analyze_escapes() do
            f_noescape(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), src.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test_broken is_return_escape(escapes.ssavalues[i])
    end

    @eval m @noinline f_returnescape(x) = broadcast(identity, x)
    let
        src, escapes = @eval m $analyze_escapes() do
            f_returnescape(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), src.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test_broken is_return_escape(escapes.ssavalues[i])
    end

    @eval m @noinline f_escape(x) = (global xx = x) # obvious escape
    let
        src, escapes = @eval m $analyze_escapes() do
            f_escape(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), src.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test is_escape(escapes.ssavalues[i])
    end

    # if we can't determine the matching method statically, we should be conservative
    let
        src, escapes = @eval m $analyze_escapes(($MutableSome{Any},)) do a
            may_exist(a)
        end
        @test is_escape(escapes.arguments[2])
    end
    let
        src, escapes = @eval m $analyze_escapes(($MutableSome{Any},)) do a
            Base.@invokelatest f_noescape(a)
        end
        @test is_escape(escapes.arguments[2])
    end

    # handling of simple union-split (just exploit the inliner's effort)
    @eval m begin
        @noinline unionsplit(_)      = string(nothing)
        @noinline unionsplit(a::Int) = a + 10
    end
    let
        src, escapes = @eval m $analyze_escapes((Union{Int,Regex},)) do a
            return unionsplit(a)
        end
        @test is_return_escape(escapes.arguments[2])
    end

    # appropriate conversion of inter-procedural context
    # https://github.com/aviatesk/EscapeAnalysis.jl/issues/7
    @eval m @noinline retescape(a) = Base.inferencebarrier(nothing)
    let
        ret = @eval m $analyze_escapes() do
            aaa = Ref("foo")   # not "return escape", should be "no escape"
            a = retescape(aaa)
            nothing
        end
        i = findfirst(==(Base.RefValue{String}), ret.ir.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test is_no_escape(ret.state.ssavalues[i])
    end
    let
        ret = @eval m $analyze_escapes() do
            aaa = Ref("foo")   # still should be "return escape"
            a = retescape(aaa)
            return aaa
        end
        i = findfirst(==(Base.RefValue{String}), ret.ir.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test is_return_escape(ret.state.ssavalues[i])
    end
end

@testset "builtins" begin
    let # throw
        r = analyze_escapes((Any,)) do a
            throw(a)
        end
        @test is_escape(r.state.arguments[2])
    end

    let # implicit throws -- currently relies on inliner's effect-freeness check
        r = analyze_escapes((Any,)) do a
            getfield(a, :may_not_field)
        end
        @test is_escape(r.state.arguments[2])

        r = analyze_escapes((Any,)) do a
            sizeof(a)
        end
        @test is_escape(r.state.arguments[2])
    end

    let # :===
        src, escapes = analyze_escapes((Any, )) do a
            c = a === nothing
            return c
        end
        @test is_return_escape(escapes.arguments[2])
    end

    let # sizeof
        src, escapes = analyze_escapes((Vector{Int}, )) do itr
            sizeof(itr)
        end
        @test is_return_escape(escapes.arguments[2])
    end

    let # ifelse
        src, escapes = analyze_escapes((Bool,)) do c
            r = ifelse(c, Ref("yes"), Ref("no"))
            return r
        end
        is = findall(==(Base.RefValue{String}), src.stmts.type) # find allocation statement
        @test !isempty(is)
        for i in is
            @test is_return_escape(escapes.ssavalues[i])
        end
    end
    let # ifelse (with constant condition)
        src, escapes = analyze_escapes((String,)) do s
            r = ifelse(isa(s, String), Ref("yes"), Ref(nothing))
            return r
        end
        is = findall(==(Base.RefValue{String}), src.stmts.type) # find allocation statement
        @test !isempty(is)
        for i in is
            @test is_return_escape(escapes.ssavalues[i])
        end
        i = findfirst(==(Base.RefValue{Nothing}), src.stmts.type) # find allocation statement
        @test !isnothing(i)
        @test is_no_escape(escapes.ssavalues[i])
    end
end

@testset "Exprs" begin
    let
        src, escapes = analyze_escapes((String,)) do s
            m = MutableSome(s)
            GC.@preserve m begin
                return nothing
            end
        end
        i = findfirst(==(MutableSome{String}), src.stmts.type) # find allocation statement
        @test !isnothing(i)
        @test is_no_escape(escapes.ssavalues[i])
    end

    let
        src, escapes = analyze_escapes((String,)) do s
            b = isdefined(s, :value)
            global bb = b
        end
        @test is_return_escape(escapes.arguments[2])
    end
end

# NOTE currently this testset relies on the special casing introduced in #16
@testset "field analysis" begin
    let
        mutable struct A
            a::Int
        end
        src, escapes = analyze_escapes((Int,)) do a
            o = A(a) # no need to escape
            f = getfield(o, :a)
            return f
        end
        i = findfirst(==(A), src.stmts.type) # allocation statement
        @assert !isnothing(i)
        @test is_no_escape(escapes.ssavalues[i])
    end

    let # an escaped tuple stmt will not propagate to its Int argument (since Int is of bitstype)
        src, escapes = analyze_escapes((Int, Any, )) do a, b
            t = tuple(a, b)
            global tt = t
            return nothing
        end
        @test is_return_escape(escapes.arguments[2])
        @test is_escape(escapes.arguments[3])
    end
end

@testset "code quality" begin
    # assert that our main routine are free from (unnecessary) runtime dispatches

    function function_filter(@nospecialize(ft))
        ft === typeof(Core.Compiler.widenconst) && return false # `widenconst` is very untyped, ignore
        ft === typeof(EscapeAnalysis.:(⊓)) && return false # `⊓` is very untyped, ignore
        ft === typeof(EscapeAnalysis.escape_builtin!) && return false # `escape_builtin!` is very untyped, ignore
        ft === typeof(isbitstype) && return false # `isbitstype` is very untyped, ignore
        return true
    end

    test_nodispatch(only(methods(EscapeAnalysis.find_escapes)).sig; function_filter)

    for m in methods(EscapeAnalysis.escape_builtin!)
        Base._methods_by_ftype(m.sig, 1, Base.get_world_counter()) === false && continue
        test_nodispatch(m.sig; function_filter)
    end
end

end # @testset "EscapeAnalysis" begin
