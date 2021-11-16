using EscapeAnalysis, Test, JET

isT(T) = (@nospecialize x) -> x === T
subT(T) = (@nospecialize x) -> x <: T
isreturn(@nospecialize x) = isa(x, Core.ReturnNode) && isdefined(x, :val)
isthrow(@nospecialize x) = Meta.isexpr(x, :call) && Core.Compiler.is_throw_call(x)

mutable struct MutableSome{T}
    value::T
end

mutable struct MutableCondition
    cond::Bool
end

@testset "EscapeAnalysis" begin

@testset "basics" begin
    let # simplest
        result = analyze_escapes((Any,)) do a # return to caller
            return nothing
        end
        @test has_return_escape(result.state.arguments[2])
    end

    let # :return
        result = analyze_escapes((Any,)) do a
            return a
        end
        @test has_return_escape(result.state.arguments[1]) # self
        @test has_return_escape(result.state.arguments[2]) # argument
    end

    let
        # global store
        result = analyze_escapes((Any,)) do a
            global aa = a
            return nothing
        end
        @test has_all_escape(result.state.arguments[2])

        # global load
        result = analyze_escapes() do
            global gr
            return gr
        end
        i = findfirst(has_return_escape, result.state.ssavalues)::Int
        has_all_escape(result.state.ssavalues[i])
        result = analyze_escapes((Any,)) do a
            global gr
            (gr::MutableSome{Any}).x = a
        end
        @test has_all_escape(result.state.arguments[2])

        # global store / load (https://github.com/aviatesk/EscapeAnalysis.jl/issues/56)
        result = analyze_escapes((Any,)) do s
            global v
            v = s
            return v
        end
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
    end

    let # :gc_preserve_begin / :gc_preserve_end
        result = analyze_escapes((String,)) do s
            m = MutableSome(s)
            GC.@preserve m begin
                return nothing
            end
        end
        i = findfirst(==(MutableSome{String}), result.ir.stmts.type) # find allocation statement
        @test !isnothing(i)
        @test has_no_escape(result.state.ssavalues[i])
    end

    let # :isdefined
        result = analyze_escapes((String, Bool, )) do a, b
            if b
                s = Ref(a)
            end
            return @isdefined(s)
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type) # find allocation statement
        @test !isnothing(i)
        @test has_no_escape(result.state.ssavalues[i])
    end

    let # :foreigncall
        result = analyze_escapes((Vector{String}, Int, )) do a, b
            return isassigned(a, b) # TODO: specialize isassigned
        end
        @test has_all_escape(result.state.arguments[2])
    end

    # https://github.com/aviatesk/EscapeAnalysis.jl/pull/16
    let # don't propagate escape information for bitypes
        result = analyze_escapes((Nothing,)) do a
            global bb = a
        end
        @test !(has_all_escape(result.state.arguments[2]))
    end
end

@testset "control flows" begin
    let # branching
        result = analyze_escapes((Any,Bool,)) do a, c
            if c
                return nothing # a doesn't escape in this branch
            else
                return a # a escapes to a caller
            end
        end
        @test has_return_escape(result.state.arguments[2])
    end

    let # π node
        result = analyze_escapes((Any,)) do a
            if isa(a, Regex)
                identity(a) # compiler will introduce π node here
                return a    # return escape !
            else
                return nothing
            end
        end
        @assert any(@nospecialize(x)->isa(x, Core.PiNode), result.ir.stmts.inst)
        @test has_return_escape(result.state.arguments[2])
    end

    let # loop
        result = analyze_escapes((Int,)) do n
            c = MutableCondition(false)
            while n > 0
                rand(Bool) && return c
            end
            nothing
        end
        i = findfirst(==(MutableCondition), result.ir.stmts.type)::Int
        @test has_return_escape(result.state.ssavalues[i])
    end

    let # exception
        result = analyze_escapes((Any,)) do a
            try
                nothing
            catch err
                return a # return escape
            end
        end
        @test has_return_escape(result.state.arguments[2])
    end
end

let # more complex
    result = analyze_escapes((Bool,)) do c
        x = Vector{MutableCondition}() # return escape
        y = MutableCondition(c) # return escape
        if c
            push!(x, y)
            return nothing
        else
            return x # return escape
        end
    end

    i = findfirst(==(Vector{MutableCondition}), result.ir.stmts.type)::Int
    @test has_return_escape(result.state.ssavalues[i])
    i = findfirst(==(MutableCondition), result.ir.stmts.type)::Int
    @test has_return_escape(result.state.ssavalues[i])
end

let # simple allocation
    result = analyze_escapes((Bool,)) do c
        mm = MutableCondition(c) # just allocated, never escapes
        return mm.cond ? nothing : 1
    end

    i = findfirst(==(MutableCondition), result.ir.stmts.type)::Int
    @test has_no_escape(result.state.ssavalues[i])
end

@testset "inter-procedural" begin
    M = Module()

    # FIXME currently we can't prove the effect-freeness of `getfield(RefValue{String}, :x)`
    # because of this check https://github.com/JuliaLang/julia/blob/94b9d66b10e8e3ebdb268e4be5f7e1f43079ad4e/base/compiler/tfuncs.jl#L745
    # and thus it leads to the following two broken tests

    @eval M @noinline broadcast_NoEscape_a(a) = (broadcast(identity, a); nothing)
    let
        result = @eval M $analyze_escapes() do
            broadcast_NoEscape_a(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type)::Int
        @test_broken has_no_escape(result.state.ssavalues[i])
    end

    @eval M @noinline broadcast_NoEscape_b(b) = broadcast(identity, b)
    let
        result = @eval M $analyze_escapes() do
            broadcast_NoEscape_b(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type)::Int
        @test_broken has_no_escape(result.state.ssavalues[i])
    end

    @eval M @noinline f_GlobalEscape_a(a) = (global globala = a) # obvious escape
    let
        result = @eval M $analyze_escapes() do
            f_GlobalEscape_a(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type)::Int
        @test has_return_escape(result.state.ssavalues[i]) && has_thrown_escape(result.state.ssavalues[i])
    end

    # if we can't determine the matching method statically, we should be conservative
    let
        result = @eval M $analyze_escapes((Ref{Any},)) do a
            may_exist(a)
        end
        @test has_all_escape(result.state.arguments[2])
    end
    let
        result = @eval M $analyze_escapes((Ref{Any},)) do a
            Base.@invokelatest broadcast_NoEscape_a(a)
        end
        @test has_all_escape(result.state.arguments[2])
    end

    # handling of simple union-split (just exploit the inliner's effort)
    @eval M begin
        @noinline unionsplit_NoEscape_a(a)      = string(nothing)
        @noinline unionsplit_NoEscape_a(a::Int) = a + 10
    end
    let
        T = Union{Int,Nothing}
        result = @eval M $analyze_escapes(($T,)) do value
            a = $MutableSome{$T}(value)
            unionsplit_NoEscape_a(a.value)
            return nothing
        end
        inds = findall(==(MutableSome{T}), result.ir.stmts.type) # find allocation statement
        @assert !isempty(inds)
        for i in inds
            @test has_no_escape(result.state.ssavalues[i])
        end
    end

    # appropriate conversion of inter-procedural context
    # https://github.com/aviatesk/EscapeAnalysis.jl/issues/7
    @eval M @noinline f_NoEscape_a(a) = (println("prevent inlining"); Base.inferencebarrier(nothing))
    let
        result = @eval M $analyze_escapes() do
            a = Ref("foo") # shouldn't be "return escape"
            b = f_NoEscape_a(a)
            nothing
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type)::Int
        @test has_no_escape(result.state.ssavalues[i])
    end
    let
        result = @eval M $analyze_escapes() do
            a = Ref("foo") # still should be "return escape"
            b = f_NoEscape_a(a)
            return a
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type)::Int
        r = findfirst(x->isa(x, Core.ReturnNode), result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.ssavalues[i], r)
    end

    # should propagate escape information imposed on return value to the aliased call argument
    @eval M @noinline f_ReturnEscape_a(a) = (println("prevent inlining"); a)
    let
        result = @eval M $analyze_escapes() do
            obj = Ref("foo")           # should be "return escape"
            ret = f_ReturnEscape_a(obj)
            return ret                 # alias of `obj`
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type)::Int
        r = findfirst(x->isa(x, Core.ReturnNode), result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.ssavalues[i], r)
    end

    @eval M @noinline f_NoReturnEscape_a(a) = (println("prevent inlining"); identity("hi"))
    let
        result = @eval M $analyze_escapes() do
            obj = Ref("foo")              # better to not be "return escape"
            ret = f_NoReturnEscape_a(obj)
            return ret                    # must not alias to `obj`
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type)::Int
        r = findfirst(x->isa(x, Core.ReturnNode), result.ir.stmts.inst)::Int
        @test !has_return_escape(result.state.ssavalues[i], r)
    end
end

@testset "builtins" begin
    let # throw
        r = analyze_escapes((Any,)) do a
            throw(a)
        end
        @test has_thrown_escape(r.state.arguments[2])
    end

    let # implicit throws
        r = analyze_escapes((Any,)) do a
            getfield(a, :may_not_field)
        end
        @test has_thrown_escape(r.state.arguments[2])

        r = analyze_escapes((Any,)) do a
            sizeof(a)
        end
        @test has_thrown_escape(r.state.arguments[2])
    end

    let # :===
        result = analyze_escapes((Bool, String)) do cond, s
            m = cond ? MutableSome(s) : nothing
            c = m === nothing
            return c
        end
        i = findfirst(==(MutableSome{String}), result.ir.stmts.type)::Int
        @test has_no_escape(result.state.ssavalues[i])
    end

    let # sizeof
        ary = [0,1,2]
        result = @eval analyze_escapes() do
            ary = $(QuoteNode(ary))
            sizeof(ary)
        end
        i = findfirst(==(Core.Const(ary)), result.ir.stmts.type)::Int
        @test has_no_escape(result.state.ssavalues[i])
    end

    let # ifelse
        result = analyze_escapes((Bool,)) do c
            r = ifelse(c, Ref("yes"), Ref("no"))
            return r
        end
        inds = findall(==(Base.RefValue{String}), result.ir.stmts.type)
        @assert !isempty(inds)
        for i in inds
            @test has_return_escape(result.state.ssavalues[i])
        end
    end
    let # ifelse (with constant condition)
        result = analyze_escapes() do
            r = ifelse(true, Ref("yes"), Ref(nothing))
            return r
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type)::Int
        @test has_return_escape(result.state.ssavalues[i])
        i = findfirst(==(Base.RefValue{Nothing}), result.ir.stmts.type)::Int
        @test has_no_escape(result.state.ssavalues[i])
    end

    let # typeassert
        result = analyze_escapes((Any,)) do x
            y = x::String
            return y
        end
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test !has_all_escape(result.state.arguments[2])
    end
end

@testset "flow-sensitivity" begin
    # ReturnEscape
    let result = analyze_escapes((Bool,)) do cond
            r = Ref("foo")
            if cond
                return cond
            end
            return r
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        rts = findall(isreturn, result.ir.stmts.inst)
        @assert length(rts) == 2
        @test count(rt->has_return_escape(result.state.ssavalues[i], rt), rts) == 1
    end
    let result = analyze_escapes((Bool,)) do cond
            r = Ref("foo")
            cnt = 0
            while rand(Bool)
                cnt += 1
                rand(Bool) && return r
            end
            rand(Bool) && return r
            return cnt
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        rts = findall(isreturn, result.ir.stmts.inst) # return statement
        @assert length(rts) == 3
        @test count(rt->has_return_escape(result.state.ssavalues[i], rt), rts) == 2
    end

    # ThrownEscape
    let result = analyze_escapes((Bool,)) do cond
            r = Ref("foo")
            if cond
                println("bar")
                return
            end
            throw(r)
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        t = findfirst(isthrow, result.ir.stmts.inst)::Int
        @test length(result.state.ssavalues[i].EscapeSites) == 1
        @test has_thrown_escape(result.state.ssavalues[i], t)
    end
    let result = analyze_escapes((Bool,)) do cond
            r = Ref("foo")
            cnt = 0
            while rand(Bool)
                cnt += 1
                if rand(Bool)
                    throw(r)
                end
            end
            if rand(Bool)
                throw(r)
            end
            return
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        ts = findall(isthrow, result.ir.stmts.inst)
        @assert length(ts) == 2
        @test all(t->has_thrown_escape(result.state.ssavalues[i], t), ts)
    end
end

@testset "field analysis" begin
    let
        result = analyze_escapes((String,)) do a # => ReturnEscape
            o = MutableSome(a) # no need to escape
            f = getfield(o, :value)
            return f
        end
        i = findfirst(isT(MutableSome{String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test_broken !has_return_escape(result.state.ssavalues[i], r)
    end

    let
        result = analyze_escapes((String,Bool)) do a, cond # => ReturnEscape &&ThrownEscape
            o = MutableSome(a) # no need to escape
            cond && throw(o)
            f = getfield(o, :value)
            return f
        end
        i = findfirst(isT(MutableSome{String}), result.ir.stmts.type)
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        t = findfirst(isthrow, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test has_thrown_escape(result.state.ssavalues[i], t)
        @test_broken !has_return_escape(result.state.ssavalues[i], r)
    end

    let
        result = analyze_escapes((String,)) do a # => ReturnEscape
            o1 = MutableSome(a) # => ReturnEscape
            o2 = MutableSome(o1) # no need to escape
            return getfield(o2, :value)
        end
        i1 = findfirst(isT(MutableSome{String}), result.ir.stmts.type)::Int
        i2 = findfirst(isT(MutableSome{MutableSome{String}}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test has_return_escape(result.state.ssavalues[i1])
        @test_broken !has_return_escape(result.state.ssavalues[i2])
    end

    let
        result = analyze_escapes((Any,Bool)) do a, cond # => ThrownEscape
            t = tuple(a) # no need to escape
            cond && throw(t[1])
            return nothing
        end
        i = findfirst(subT(Tuple), result.ir.stmts.type)::Int
        t = findfirst(isthrow, result.ir.stmts.inst)::Int
        @test has_thrown_escape(result.state.arguments[2], t)
        @test_broken !has_thrown_escape(result.state.ssavalues[i], t)
    end
end

# demonstrate a simple type level analysis can sometimes improve the analysis accuracy
# by compensating the lack of yet unimplemented analyses
@testset "special-casing bitstype" begin
    let result = analyze_escapes((Int,)) do a
            o = MutableSome(a) # no need to escape
            f = getfield(o, :value)
            return f
        end
        i = findfirst(isT(MutableSome{Int}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test !has_return_escape(result.state.ssavalues[i], r)
    end

    # an escaped tuple stmt will not propagate to its Int argument (since `Int` is of bitstype)
    let result = analyze_escapes((Int,Any,)) do a, b
            t = tuple(a, b)
            return t
        end
        i = findfirst(subT(Tuple), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test !has_return_escape(result.state.arguments[2], r)
        @test has_return_escape(result.state.arguments[3], r)
    end
end

@testset "finalizer elision" begin
    @test can_elide_finalizer(EscapeAnalysis.NoEscape(), 1)
    @test !can_elide_finalizer(EscapeAnalysis.ReturnEscape(1), 1)
    @test can_elide_finalizer(EscapeAnalysis.ReturnEscape(1), 2)
    @test !can_elide_finalizer(EscapeAnalysis.ArgumentReturnEscape(), 1)
    @test can_elide_finalizer(EscapeAnalysis.ThrownEscape(1), 1)
end

# # TODO implement a finalizer elision pass
# mutable struct WithFinalizer
#     v
#     function WithFinalizer(v)
#         x = new(v)
#         f(t) = @async println("Finalizing $t.")
#         return finalizer(x, x)
#     end
# end
# make_m(v = 10) = MyMutable(v)
# function simple(cond)
#     m = make_m()
#     if cond
#         # println(m.v)
#         return nothing # <= insert `finalize` call here
#     end
#     return m
# end

@testset "code quality" begin
    # assert that our main routine are free from (unnecessary) runtime dispatches

    function function_filter(@nospecialize(ft))
        ft === typeof(Core.Compiler.widenconst) && return false # `widenconst` is very untyped, ignore
        ft === typeof(EscapeAnalysis.escape_builtin!) && return false # `escape_builtin!` is very untyped, ignore
        return true
    end

    test_opt(only(methods(EscapeAnalysis.find_escapes)).sig; function_filter)
    for m in methods(EscapeAnalysis.escape_builtin!)
        Base._methods_by_ftype(m.sig, 1, Base.get_world_counter()) === false && continue
        test_opt(m.sig; function_filter)
    end
end

end # @testset "EscapeAnalysis" begin
