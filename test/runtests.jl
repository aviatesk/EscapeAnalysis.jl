using EscapeAnalysis, InteractiveUtils, Test, JET

mutable struct MutableSome{T}
    value::T
end

mutable struct MutableCondition
    cond::Bool
end

mutable struct MutableFields{S,T}
    field1::S
    field2::T
end

@testset "EscapeAnalysis" begin

@testset "basics" begin
    let # simplest
        result = analyze_escapes((Any,)) do a # return to caller
            return nothing
        end
        @test has_return_escape(result.state.arguments[2])
    end

    let # return
        result = analyze_escapes((Any,)) do a
            return a
        end
        @test has_return_escape(result.state.arguments[1]) # self
        @test has_return_escape(result.state.arguments[2]) # argument
    end

    let # global store
        result = analyze_escapes((Any,)) do a
            global aa = a
            return nothing
        end
        @test has_global_escape(result.state.arguments[2])
    end

    let # global load
        result = analyze_escapes() do
            global gr
            return gr
        end
        i = findfirst(has_return_escape, result.state.ssavalues)
        @assert !isnothing(i)
        has_global_escape(result.state.ssavalues[i])

        result = analyze_escapes((Any,)) do a
            global gr
            (gr::MutableSome{Any}).x = a
        end
        @test has_global_escape(result.state.arguments[2])
    end

    # https://github.com/aviatesk/EscapeAnalysis.jl/pull/16
    let # don't propagate escape information for bitypes
        result = analyze_escapes((Nothing,)) do a
            global bb = a
        end
        @test !(has_global_escape(result.state.arguments[2]))
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
        i = findfirst(==(MutableCondition), result.ir.stmts.type)
        @assert !isnothing(i)
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

    i = findfirst(==(Vector{MutableCondition}), result.ir.stmts.type)
    @assert !isnothing(i)
    @test has_return_escape(result.state.ssavalues[i])
    i = findfirst(==(MutableCondition), result.ir.stmts.type)
    @assert !isnothing(i)
    @test has_return_escape(result.state.ssavalues[i])
end

let # simple allocation
    result = analyze_escapes((Bool,)) do c
        mm = MutableCondition(c) # just allocated, never escapes
        return mm.cond ? nothing : 1
    end

    i = findfirst(==(MutableCondition), result.ir.stmts.type) # allocation statement
    @assert !isnothing(i)
    @test has_no_escape(result.state.ssavalues[i])
end

@testset "inter-procedural" begin
    m = Module()

    # FIXME currently we can't prove the effect-freeness of `getfield(RefValue{String}, :x)`
    # because of this check https://github.com/JuliaLang/julia/blob/94b9d66b10e8e3ebdb268e4be5f7e1f43079ad4e/base/compiler/tfuncs.jl#L745
    # and thus it leads to the following two broken tests

    @eval m @noinline f_no_escape(x) = (broadcast(identity, x); nothing)
    let
        result = @eval m $analyze_escapes() do
            f_no_escape(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test_broken has_no_escape(result.state.ssavalues[i])
    end

    @eval m @noinline f_no_escape2(x) = broadcast(identity, x)
    let
        result = @eval m $analyze_escapes() do
            f_no_escape2(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test_broken has_no_escape(result.state.ssavalues[i])
    end

    @eval m @noinline f_global_escape(x) = (global xx = x) # obvious escape
    let
        result = @eval m $analyze_escapes() do
            f_global_escape(Ref("Hi"))
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test has_global_escape(result.state.ssavalues[i])
    end

    # if we can't determine the matching method statically, we should be conservative
    let
        result = @eval m $analyze_escapes((Ref{Any},)) do a
            may_exist(a)
        end
        @test has_all_escape(result.state.arguments[2])
    end
    let
        result = @eval m $analyze_escapes((Ref{Any},)) do a
            Base.@invokelatest f_no_escape(a)
        end
        @test has_all_escape(result.state.arguments[2])
    end

    # handling of simple union-split (just exploit the inliner's effort)
    @eval m begin
        @noinline unionsplit_noescape(_)      = string(nothing)
        @noinline unionsplit_noescape(a::Int) = a + 10
    end
    let
        T = Union{Int,Nothing}
        result = @eval m $analyze_escapes(($T,)) do value
            a = $MutableSome{$T}(value)
            unionsplit_noescape(a.value)
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
    @eval m @noinline f_no_escape_simple(a) = Base.inferencebarrier(nothing)
    let
        result = @eval m $analyze_escapes() do
            aaa = Ref("foo") # shouldn't be "return escape"
            a = f_no_escape_simple(aaa)
            nothing
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test has_no_escape(result.state.ssavalues[i])
    end
    let
        result = @eval m $analyze_escapes() do
            aaa = Ref("foo") # still should be "return escape"
            a = f_no_escape_simple(aaa)
            return aaa
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type) # find allocation statement
        r = findfirst(x->isa(x, Core.ReturnNode), result.ir.stmts.inst)
        @assert !isnothing(i) && !isnothing(r)
        @test has_return_escape(result.state.ssavalues[i], r)
    end

    # should propagate escape information imposed on return value to the aliased call argument
    @eval m @noinline f_return_escape(a) = a
    let
        result = @eval m $analyze_escapes() do
            obj = Ref("foo")           # should be "return escape"
            ret = @noinline f_return_escape(obj)
            return ret                 # alias of `obj`
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type) # find allocation statement
        r = findfirst(x->isa(x, Core.ReturnNode), result.ir.stmts.inst)
        @assert !isnothing(i) && !isnothing(r)
        @test has_return_escape(result.state.ssavalues[i], r)
    end

    @eval m @noinline f_no_return_escape(a) = identity("hi")
    let
        result = @eval m $analyze_escapes() do
            obj = Ref("foo")              # better to not be "return escape"
            ret = @noinline f_no_return_escape(obj)
            return ret                    # must not alias to `obj`
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type) # find allocation statement
        r = findfirst(x->isa(x, Core.ReturnNode), result.ir.stmts.inst)
        @assert !isnothing(i) && !isnothing(r)
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
        i = findfirst(==(MutableSome{String}), result.ir.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test has_no_escape(result.state.ssavalues[i])
    end

    let # sizeof
        ary = [0,1,2]
        result = @eval analyze_escapes() do
            ary = $(QuoteNode(ary))
            sizeof(ary)
        end
        i = findfirst(==(Core.Const(ary)), result.ir.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test has_no_escape(result.state.ssavalues[i])
    end

    let # ifelse
        result = analyze_escapes((Bool,)) do c
            r = ifelse(c, Ref("yes"), Ref("no"))
            return r
        end
        inds = findall(==(Base.RefValue{String}), result.ir.stmts.type) # find allocation statement
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
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test has_return_escape(result.state.ssavalues[i])
        i = findfirst(==(Base.RefValue{Nothing}), result.ir.stmts.type) # find allocation statement
        @assert !isnothing(i)
        @test has_no_escape(result.state.ssavalues[i])
    end

    let # typeassert
        result = analyze_escapes((Any,)) do x
            y = x::String
            return y
        end
        r = findfirst(x->isa(x,Core.ReturnNode), result.ir.stmts.inst)
        @assert !isnothing(r)
        @test has_return_escape(result.state.arguments[2], r)
        @test !has_all_escape(result.state.arguments[2])
    end
end

@testset "Exprs" begin
    let
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
end

@testset "field analysis" begin
    let
        result = analyze_escapes((String,)) do a # => ReturnEscape
            o = MutableSome(a) # no need to escape
            f = getfield(o, :value)
            return f
        end
        i = findfirst(==(MutableSome{String}), result.ir.stmts.type)
        r = findfirst(x->isa(x, Core.ReturnNode), result.ir.stmts.inst)
        @assert !isnothing(i) && !isnothing(r)
        @test has_return_escape(result.state.arguments[2], r)
        @test !has_return_escape(result.state.ssavalues[i], r)
    end

    let
        result = analyze_escapes((String,)) do a # => ReturnEscape && GlobalEscape
            o = MutableSome(a) # no need to escape
            global oo = o
            f = getfield(o, :value)
            return f
        end
        i = findfirst(==(MutableSome{String}), result.ir.stmts.type)
        r = findfirst(x->isa(x, Core.ReturnNode), result.ir.stmts.inst)
        @assert !isnothing(i) && !isnothing(r)
        @test has_return_escape(result.state.arguments[2], r)
        @test has_global_escape(result.state.ssavalues[i])
        @test !has_return_escape(result.state.ssavalues[i], r)
    end

    let # nested unwrap
        result = analyze_escapes((String,)) do a # => ReturnEscape
            o1 = MutableSome(a) # => ReturnEscape
            o2 = MutableSome(o1) # no need to escape
            return getfield(o2, :value)
        end
        i1 = findfirst(==(MutableSome{String}), result.ir.stmts.type)
        i2 = findfirst(==(MutableSome{MutableSome{String}}), result.ir.stmts.type)
        r = findfirst(x->isa(x, Core.ReturnNode), result.ir.stmts.inst)
        @assert !isnothing(i1) && !isnothing(i2) && !isnothing(4)
        @test has_return_escape(result.state.arguments[2], r)
        @test has_return_escape(result.state.ssavalues[i1], r)
        @test !has_return_escape(result.state.ssavalues[i2], r)
    end

    let # TODO nested wrap (NOTE: we're interested in the value of field)
        result = analyze_escapes((String,)) do a # => ReturnEscape
            o1  = MutableSome(a)        # => ReturnEscape
            o2  = MutableSome(o1)       # => NoEscape
            o1′ = getfield(o2, :value)  # => FieldEscapes(ReturnEscape)
            a′  = getfield(o1′, :value) # => ReturnEscape
            return a′
        end
    end

    let # multiple fields
        result = analyze_escapes((String, String)) do a, b # => ReturnEscape, ReturnEscape
            obj = MutableFields(a, b) # => NoEscape
            fld1 = obj.field1
            fld2 = obj.field2
            return (fld1, fld2)
        end
        i = findfirst(==(MutableFields{String,String}), result.ir.stmts.type)
        r = findfirst(x->isa(x, Core.ReturnNode), result.ir.stmts.inst)
        @assert !isnothing(i) && !isnothing(r)
        @test has_return_escape(result.state.arguments[2], r) # a
        @test has_return_escape(result.state.arguments[3], r) # b
        @test !has_return_escape(result.state.ssavalues[i], r)
    end

    let
        result = analyze_escapes((Any,)) do a # => GlobalEscape
            t = tuple(a) # no need to escape
            global tt = t[1]
            return nothing
        end
        i = findfirst(t->t<:Tuple, result.ir.stmts.type) # allocation statement
        @assert !isnothing(i)
        @test has_global_escape(result.state.arguments[2])
        @test !has_global_escape(result.state.ssavalues[i])
    end

    let # inter-procedural conversion
        m = Module()
        @eval m @noinline getvalue(obj) = obj.value
        result = @eval m $analyze_escapes((String,)) do a # => ReturnEscape
            obj = $MutableSome(a) # no need to escape
            fld = getvalue(obj)
            return fld
        end
        i = findfirst(==(MutableSome{String}), result.ir.stmts.type)
        r = findfirst(x->isa(x, Core.ReturnNode), result.ir.stmts.inst)
        @assert !isnothing(i) && !isnothing(r)
        @test has_return_escape(result.state.arguments[2], r)
        @test !has_return_escape(result.state.ssavalues[i], r)
    end

    let # `popfirst!(InvasiveLinkedList{Task})` within this `println` used to cause infinite loop ...
        result = analyze_escapes((String,)) do a
            println(a)
            nothing
        end
        @test true
    end
end

# demonstrate a simple type level analysis can sometimes compensate the lack of yet unimplemented analysis
@testset "special-casing bitstype" begin
    let # an escaped tuple stmt will not propagate to its Int argument (since Int is of bitstype)
        result = analyze_escapes((Int, Any, )) do a, b
            t = tuple(a, b)
            global tt = t
            return nothing
        end
        @test has_return_escape(result.state.arguments[2])
        @test has_global_escape(result.state.arguments[3])
    end
end

@testset "return flow-sensitivity" begin
    isa2(T) = x->isa(x,T)

    let
        result = analyze_escapes((Bool,)) do cond
            r = Ref("foo")
            if cond
                return cond
            end
            return r
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type) # allocation statement
        @assert !isnothing(i)
        rts = findall(isa2(Core.ReturnNode), result.ir.stmts.inst) # return statement
        @assert length(rts) == 2
        @test count(rt->has_return_escape(result.state.ssavalues[i], rt), rts) == 1
    end

    let
        result = analyze_escapes((Bool,)) do cond
            r = Ref("foo")
            cnt = 0
            while rand(Bool)
                cnt += 1
                rand(Bool) && return r
            end
            rand(Bool) && return r
            return cnt
        end
        i = findfirst(==(Base.RefValue{String}), result.ir.stmts.type) # allocation statement
        @assert !isnothing(i)
        rts = findall(isa2(Core.ReturnNode), result.ir.stmts.inst) # return statement
        @assert length(rts) == 3
        @test count(rt->has_return_escape(result.state.ssavalues[i], rt), rts) == 2
    end
end

# TODO
mutable struct WithFinalizer
    v
    function WithFinalizer(v)
        x = new(v)
        f(t) = @async println("Finalizing $t.")
        return finalizer(x, x)
    end
end
make_m(v = 10) = MyMutable(v)
function simple(cond)
    m = make_m()
    if cond
        # println(m.v)
        return nothing # <= insert `finalize` call here
    end
    return m
end

@testset "finalizer elision" begin
    @test can_elide_finalizer(EscapeAnalysis.NoEscape(), 1)
    @test !can_elide_finalizer(EscapeAnalysis.ReturnEscape(1), 1)
    @test can_elide_finalizer(EscapeAnalysis.ReturnEscape(1), 2)
    @test !can_elide_finalizer(EscapeAnalysis.ArgumentReturnEscape(), 1)
    @test !can_elide_finalizer(EscapeAnalysis.GlobalEscape(), 1)
    @test can_elide_finalizer(EscapeAnalysis.ThrownEscape(), 1)
end

@testset "code quality" begin
    # assert that our main routine are free from (unnecessary) runtime dispatches

    function function_filter(@nospecialize(ft))
        ft === typeof(Core.Compiler.widenconst) && return false # `widenconst` is very untyped, ignore
        ft === typeof(EscapeAnalysis.escape_builtin!) && return false # `escape_builtin!` is very untyped, ignore
        ft === typeof(isbitstype) && return false # `isbitstype` is very untyped, ignore
        return true
    end

    test_opt(only(methods(EscapeAnalysis.find_escapes)).sig; function_filter)
    for m in methods(EscapeAnalysis.escape_builtin!)
        Base._methods_by_ftype(m.sig, 1, Base.get_world_counter()) === false && continue
        test_opt(m.sig; function_filter)
    end
end

end # @testset "EscapeAnalysis" begin
