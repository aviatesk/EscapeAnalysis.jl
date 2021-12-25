using EscapeAnalysis, Test, JET

isT(T) = (@nospecialize x) -> x === T
issubT(T) = (@nospecialize x) -> x <: T
isreturn(@nospecialize x) = isa(x, Core.ReturnNode) && isdefined(x, :val)
isthrow(@nospecialize x) = Meta.isexpr(x, :call) && Core.Compiler.is_throw_call(x)
isnew(@nospecialize x) = Meta.isexpr(x, :new)
isϕ(@nospecialize x) = isa(x, Core.PhiNode)
import Core.Compiler: argextype, singleton_type
const EMPTY_SPTYPES = Any[]
iscall(y) = @nospecialize(x) -> iscall(y, x)
function iscall((ir, f), @nospecialize(x))
    return iscall(x) do @nospecialize x
        Core.Compiler.singleton_type(Core.Compiler.argextype(x, ir, EMPTY_SPTYPES)) === f
    end
end
iscall(pred::Function, @nospecialize(x)) = Meta.isexpr(x, :call) && pred(x.args[1])

let setup_ex = quote
        mutable struct SafeRef{T}
            x::T
        end
        Base.getindex(s::SafeRef) = getfield(s, 1)
        Base.setindex!(s::SafeRef, x) = setfield!(s, 1, x)

        mutable struct SafeRefs{S,T}
            x1::S
            x2::T
        end
        Base.getindex(s::SafeRefs, idx::Int) = getfield(s, idx)
        Base.setindex!(s::SafeRefs, x, idx::Int) = setfield!(s, idx, x)
    end
    global function EATModule(setup_ex = setup_ex)
        M = Module()
        Core.eval(M, setup_ex)
        return M
    end
    Core.eval(@__MODULE__, setup_ex)
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
        i = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[1], 0) # self
        @test !has_return_escape(result.state.arguments[1], i) # self
        @test has_return_escape(result.state.arguments[2], 0) # a
        @test has_return_escape(result.state.arguments[2], i) # a
    end
    let # global store
        result = analyze_escapes((Any,)) do a
            global aa = a
            nothing
        end
        @test has_all_escape(result.state.arguments[2])
    end
    let # global load
        result = analyze_escapes() do
            global gr
            return gr
        end
        i = findfirst(has_return_escape, result.state.ssavalues)::Int
        has_all_escape(result.state.ssavalues[i])
    end
    let # global store / load (https://github.com/aviatesk/EscapeAnalysis.jl/issues/56)
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
            m = SafeRef(s)
            GC.@preserve m begin
                return nothing
            end
        end
        i = findfirst(isT(SafeRef{String}), result.ir.stmts.type) # find allocation statement
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
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type) # find allocation statement
        @test !isnothing(i)
        @test has_no_escape(result.state.ssavalues[i])
    end
    let # :foreigncall
        result = analyze_escapes((Vector{String}, Int, )) do a, b
            return isassigned(a, b) # TODO: specialize isassigned
        end
        @test has_all_escape(result.state.arguments[2])
    end
    let # ϕ-node
        result = analyze_escapes((Bool,Any,Any)) do cond, a, b
            c = cond ? a : b # ϕ(a, b)
            return c
        end
        @assert any(@nospecialize(x)->isa(x, Core.PhiNode), result.ir.stmts.inst)
        i = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[3], i) # a
        @test has_return_escape(result.state.arguments[4], i) # b
    end
    let # π-node
        result = analyze_escapes((Any,)) do a
            if isa(a, Regex) # a::π(Regex)
                return a
            end
            return nothing
        end
        @assert any(@nospecialize(x)->isa(x, Core.PiNode), result.ir.stmts.inst)
        i = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], i)
    end
    let # φᶜ-node / ϒ-node
        result = analyze_escapes((Any,String)) do a, b
            local x::String
            try
                x = a
            catch err
                x = b
            end
            return x
        end
        @assert any(@nospecialize(x)->isa(x, Core.PhiCNode), result.ir.stmts.inst)
        @assert any(@nospecialize(x)->isa(x, Core.UpsilonNode), result.ir.stmts.inst)
        i = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], i)
        @test has_return_escape(result.state.arguments[3], i)
    end
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
    let # loop
        result = analyze_escapes((Int,)) do n
            c = SafeRef{Bool}(false)
            while n > 0
                rand(Bool) && return c
            end
            nothing
        end
        i = findfirst(isT(SafeRef{Bool}), result.ir.stmts.type)::Int
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
        x = Vector{SafeRef{Bool}}() # return escape
        y = SafeRef{Bool}(c) # return escape
        if c
            push!(x, y)
            return nothing
        else
            return x # return escape
        end
    end

    i = findfirst(isT(Vector{SafeRef{Bool}}), result.ir.stmts.type)::Int
    @test has_return_escape(result.state.ssavalues[i])
    i = findfirst(isT(SafeRef{Bool}), result.ir.stmts.type)::Int
    @test has_return_escape(result.state.ssavalues[i])
end

let # simple allocation
    result = analyze_escapes((Bool,)) do c
        mm = SafeRef{Bool}(c) # just allocated, never escapes
        return mm[] ? nothing : 1
    end

    i = findfirst(isT(SafeRef{Bool}), result.ir.stmts.type)::Int
    @test has_no_escape(result.state.ssavalues[i])
end

@testset "inter-procedural" begin
    # FIXME currently we can't prove the effect-freeness of `getfield(RefValue{String}, :x)`
    # because of this check https://github.com/JuliaLang/julia/blob/94b9d66b10e8e3ebdb268e4be5f7e1f43079ad4e/base/compiler/tfuncs.jl#L745
    # and thus it leads to the following two broken tests
    let result = @eval Module() begin
            @noinline broadcast_NoEscape(a) = (broadcast(identity, a); nothing)
            $analyze_escapes() do
                broadcast_NoEscape(Ref("Hi"))
            end
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        @test_broken has_no_escape(result.state.ssavalues[i])
    end
    let result = @eval Module() begin
            @noinline broadcast_NoEscape2(b) = broadcast(identity, b)
            $analyze_escapes() do
                broadcast_NoEscape2(Ref("Hi"))
            end
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        @test_broken has_no_escape(result.state.ssavalues[i])
    end
    let result = @eval Module() begin
            @noinline f_GlobalEscape_a(a) = (global globala = a) # obvious escape
            $analyze_escapes() do
                f_GlobalEscape_a(Ref("Hi"))
            end
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        @test has_return_escape(result.state.ssavalues[i]) && has_thrown_escape(result.state.ssavalues[i])
    end
    # if we can't determine the matching method statically, we should be conservative
    let result = @eval Module() $analyze_escapes((Ref{Any},)) do a
            may_exist(a)
        end
        @test has_all_escape(result.state.arguments[2])
    end
    let result = @eval Module() begin
            @noinline broadcast_NoEscape(a) = (broadcast(identity, a); nothing)
            $analyze_escapes((Ref{Any},)) do a
                Base.@invokelatest broadcast_NoEscape(a)
            end
        end
        @test has_all_escape(result.state.arguments[2])
    end

    # handling of simple union-split (just exploit the inliner's effort)
    let T = Union{Int,Nothing}
        result = @eval Module() begin
            @noinline unionsplit_NoEscape_a(a)      = string(nothing)
            @noinline unionsplit_NoEscape_a(a::Int) = a + 10
            $analyze_escapes(($T,)) do x
                s = $SafeRef{$T}(x)
                unionsplit_NoEscape_a(s[])
                return nothing
            end
        end
        inds = findall(isT(SafeRef{T}), result.ir.stmts.type) # find allocation statement
        @assert !isempty(inds)
        for i in inds
            @test has_no_escape(result.state.ssavalues[i])
        end
    end

    # appropriate conversion of inter-procedural context
    # https://github.com/aviatesk/EscapeAnalysis.jl/issues/7
    let M = Module()
        @eval M @noinline f_NoEscape_a(a) = (println("prevent inlining"); Base.inferencebarrier(nothing))

        result = @eval M $analyze_escapes() do
            a = Ref("foo") # shouldn't be "return escape"
            b = f_NoEscape_a(a)
            nothing
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        @test has_no_escape(result.state.ssavalues[i])

        result = @eval M $analyze_escapes() do
            a = Ref("foo") # still should be "return escape"
            b = f_NoEscape_a(a)
            return a
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.ssavalues[i], r)
    end

    # should propagate escape information imposed on return value to the aliased call argument
    let result = @eval Module() begin
            @noinline f_ReturnEscape_a(a) = (println("prevent inlining"); a)
            $analyze_escapes() do
                obj = Ref("foo")           # should be "return escape"
                ret = f_ReturnEscape_a(obj)
                return ret                 # alias of `obj`
            end
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.ssavalues[i], r)
    end
    let result = @eval Module() begin
            @noinline f_NoReturnEscape_a(a) = (println("prevent inlining"); identity("hi"))
            $analyze_escapes() do
                obj = Ref("foo")              # better to not be "return escape"
                ret = f_NoReturnEscape_a(obj)
                return ret                    # must not alias to `obj`
            end
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
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
            m = cond ? SafeRef(s) : nothing
            c = m === nothing
            return c
        end
        i = findfirst(isT(SafeRef{String}), result.ir.stmts.type)::Int
        @test has_no_escape(result.state.ssavalues[i])
    end

    let # sizeof
        ary = [0,1,2]
        result = @eval analyze_escapes() do
            ary = $(QuoteNode(ary))
            sizeof(ary)
        end
        i = findfirst(isT(Core.Const(ary)), result.ir.stmts.type)::Int
        @test has_no_escape(result.state.ssavalues[i])
    end

    let # ifelse
        result = analyze_escapes((Bool,)) do c
            r = ifelse(c, Ref("yes"), Ref("no"))
            return r
        end
        inds = findall(isT(Base.RefValue{String}), result.ir.stmts.type)
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
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        @test has_return_escape(result.state.ssavalues[i])
        i = findfirst(isT(Base.RefValue{Nothing}), result.ir.stmts.type)::Int
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

    let # isdefined
        result = analyze_escapes((Any,)) do x
            isdefined(x, :foo) ? x : throw("undefined")
        end
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test !has_all_escape(result.state.arguments[2])

        result = analyze_escapes((Module,)) do m
            isdefined(m, 10) # throws
        end
        @test has_thrown_escape(result.state.arguments[2])
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

@testset "field analysis / alias analysis" begin
    # escaped allocations
    # -------------------

    # escaped object should escape its fields as well
    let result = analyze_escapes((Any,)) do a
            global g = SafeRef{Any}(a)
            nothing
        end
        i = findfirst(isT(SafeRef{Any}), result.ir.stmts.type)::Int
        @test has_all_escape(result.state.ssavalues[i])
        @test has_all_escape(result.state.arguments[2])
    end
    let result = analyze_escapes((Any,)) do a
            global g = (a,)
            nothing
        end
        i = findfirst(issubT(Tuple), result.ir.stmts.type)::Int
        @test has_all_escape(result.state.ssavalues[i])
        @test has_all_escape(result.state.arguments[2])
    end
    let result = analyze_escapes((Any,)) do a
            o0 = SafeRef{Any}(a)
            global g = SafeRef(o0)
            nothing
        end
        i0 = findfirst(isT(SafeRef{Any}), result.ir.stmts.type)::Int
        i1 = findfirst(isT(SafeRef{SafeRef{Any}}), result.ir.stmts.type)::Int
        @test has_all_escape(result.state.ssavalues[i0])
        @test has_all_escape(result.state.ssavalues[i1])
        @test has_all_escape(result.state.arguments[2])
    end
    let result = analyze_escapes((Any,)) do a
            t0 = (a,)
            global g = (t0,)
            nothing
        end
        inds = findall(issubT(Tuple), result.ir.stmts.type)
        @assert length(inds) == 2
        for i in inds; @test has_all_escape(result.state.ssavalues[i]); end
        @test has_all_escape(result.state.arguments[2])
    end
    # global escape through `setfield!`
    let result = analyze_escapes((Any,)) do a
            r = SafeRef{Any}(:init)
            global g = r
            r[] = a
            nothing
        end
        i = findfirst(isT(SafeRef{Any}), result.ir.stmts.type)::Int
        @test has_all_escape(result.state.ssavalues[i])
        @test has_all_escape(result.state.arguments[2])
    end
    let result = analyze_escapes((Any,Any)) do a, b
            r = SafeRef{Any}(a)
            global g = r
            r[] = b
            nothing
        end
        i = findfirst(isT(SafeRef{Any}), result.ir.stmts.type)::Int
        @test has_all_escape(result.state.ssavalues[i])
        @test has_all_escape(result.state.arguments[2]) # a
        @test has_all_escape(result.state.arguments[3]) # b
    end
    let result = @eval EATModule() begin
            const Rx = SafeRef{String}("Rx")
            $analyze_escapes((String,)) do s
                Rx[] = s
                Core.sizeof(Rx[])
            end
        end
        @test has_all_escape(result.state.arguments[2])
    end
    let result = @eval EATModule() begin
            const Rx = SafeRef{String}("Rx")
            $analyze_escapes((String,)) do s
                setfield!(Rx, :x, s)
                Core.sizeof(Rx[])
            end
        end
        @test has_all_escape(result.state.arguments[2])
    end
    let M = EATModule()
        @eval M module ___xxx___
            import ..SafeRef
            const Rx = SafeRef("Rx")
        end
        result = @eval M begin
            $analyze_escapes((String,)) do s
                rx = getfield(___xxx___, :Rx)
                rx[] = s
                nothing
            end
        end
        @test has_all_escape(result.state.arguments[2])
    end

    # field escape
    # ------------

    # field escape should propagate to :new arguments
    let result = analyze_escapes((String,)) do a
            o = SafeRef(a)
            f = o[]
            return f
        end
        i = findfirst(isT(SafeRef{String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test is_sroa_eligible(result.state.ssavalues[i])
    end
    let result = analyze_escapes((String,)) do a
            t = (a,)
            f = t[1]
            return f
        end
        i = findfirst(t->t<:Tuple, result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test is_sroa_eligible(result.state.ssavalues[i])
    end
    let result = analyze_escapes((String, String)) do a, b
            obj = SafeRefs(a, b)
            fld1 = obj[1]
            fld2 = obj[2]
            return (fld1, fld2)
        end
        i = findfirst(isT(SafeRefs{String,String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r) # a
        @test has_return_escape(result.state.arguments[3], r) # b
        @test is_sroa_eligible(result.state.ssavalues[i])
    end

    # field escape should propagate to `setfield!` argument
    let result = analyze_escapes((String,)) do a
            o = SafeRef("foo")
            o[] = a
            f = o[]
            return f
        end
        i = findfirst(isT(SafeRef{String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test is_sroa_eligible(result.state.ssavalues[i])
    end
    # propagate escape information imposed on return value of `setfield!` call
    let result = analyze_escapes((String,)) do a
            obj = SafeRef("foo")
            return (obj[] = a)
        end
        i = findfirst(isT(SafeRef{String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test is_sroa_eligible(result.state.ssavalues[i])
    end

    # nested allocations
    let result = analyze_escapes((String,)) do a
            o1 = SafeRef(a)
            o2 = SafeRef(o1)
            return o2[]
        end
        i1 = findfirst(isT(SafeRef{String}), result.ir.stmts.type)::Int
        i2 = findfirst(isT(SafeRef{SafeRef{String}}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test has_return_escape(result.state.ssavalues[i1], r)
        @test is_sroa_eligible(result.state.ssavalues[i2])
    end
    let result = analyze_escapes((String,)) do a
            o1 = (a,)
            o2 = (o1,)
            return o2[1]
        end
        i1 = findfirst(isT(Tuple{String}), result.ir.stmts.type)::Int
        i2 = findfirst(isT(Tuple{Tuple{String}}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test has_return_escape(result.state.ssavalues[i1], r)
        @test is_sroa_eligible(result.state.ssavalues[i2])
    end
    let result = analyze_escapes((String,)) do a
            o1  = SafeRef(a)
            o2  = SafeRef(o1)
            o1′ = o2[]
            a′  = o1′[]
            return a′
        end
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        for i in findall(isnew, result.ir.stmts.inst)
            @test is_sroa_eligible(result.state.ssavalues[i])
        end
    end
    let result = analyze_escapes((String,)) do x
            broadcast(identity, Ref(x))
        end
        i = findfirst(isT(Base.RefValue{String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        @test is_sroa_eligible(result.state.ssavalues[i])
    end

    # ϕ-node allocations
    let result = analyze_escapes((Bool,Any,Any)) do cond, x, y
            if cond
                ϕ = SafeRef{Any}(x)
            else
                ϕ = SafeRef{Any}(y)
            end
            return ϕ[]
        end
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[3], r) # x
        @test has_return_escape(result.state.arguments[4], r) # y
        i = findfirst(isϕ, result.ir.stmts.inst)::Int
        @test is_sroa_eligible(result.state.ssavalues[i])
        for i in findall(isnew, result.ir.stmts.inst)
            @test is_sroa_eligible(result.state.ssavalues[i])
        end
    end
    let result = analyze_escapes((Bool,Any,Any)) do cond, x, y
            if cond
                ϕ2 = ϕ1 = SafeRef{Any}(x)
            else
                ϕ2 = ϕ1 = SafeRef{Any}(y)
            end
            return ϕ1[], ϕ2[]
        end
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[3], r) # x
        @test has_return_escape(result.state.arguments[4], r) # y
        for i in findall(isϕ, result.ir.stmts.inst)
            @test is_sroa_eligible(result.state.ssavalues[i])
        end
        for i in findall(isnew, result.ir.stmts.inst)
            @test is_sroa_eligible(result.state.ssavalues[i])
        end
    end

    # alias analysis
    # --------------

    # alias via getfield & Expr(:new)
    let result = @eval EATModule() begin
            const Rx = SafeRef("Rx")
            $analyze_escapes((String,)) do s
                r = SafeRef(Rx)
                rx = r[] # rx aliased to Rx
                rx[] = s
                nothing
            end
        end
        i = findfirst(isnew, result.ir.stmts.inst)
        @test has_all_escape(result.state.arguments[2])
        @test is_sroa_eligible(result.state.ssavalues[i])
    end
    # alias via getfield & setfield!
    let result = @eval EATModule() begin
            const Rx = SafeRef("Rx")
            $analyze_escapes((SafeRef{String}, String,)) do _rx, s
                r = SafeRef(_rx)
                r[] = Rx
                rx = r[] # rx aliased to Rx
                rx[] = s
                nothing
            end
        end
        i = findfirst(isnew, result.ir.stmts.inst)
        @test has_all_escape(result.state.arguments[3])
        @test is_sroa_eligible(result.state.ssavalues[i])
    end
    # alias via typeassert
    let result = analyze_escapes((Any,)) do a
            global g
            (g::SafeRef{Any})[] = a
            nothing
        end
        @test has_all_escape(result.state.arguments[2])
    end
    # alias via ifelse
    let result = @eval EATModule() begin
            const Lx, Rx = SafeRef("Lx"), SafeRef("Rx")
            $analyze_escapes((Bool,String,)) do c, a
                r = ifelse(c, Lx, Rx)
                r[] = a
                nothing
            end
        end
        @test has_all_escape(result.state.arguments[3]) # a
    end
    # alias via ϕ-node
    let result = analyze_escapes((Bool,String)) do cond, x
            if cond
                ϕ2 = ϕ1 = SafeRef("foo")
            else
                ϕ2 = ϕ1 = SafeRef("bar")
            end
            ϕ2[] = x
            return ϕ1[]
        end
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[3], r) # x
        i = findfirst(isϕ, result.ir.stmts.inst)::Int
        @test is_sroa_eligible(result.state.ssavalues[i])
        for i in findall(isnew, result.ir.stmts.inst)
            @test is_sroa_eligible(result.state.ssavalues[i])
        end
    end
    let result = analyze_escapes((Bool,Bool,String)) do cond1, cond2, x
            if cond1
                ϕ2 = ϕ1 = SafeRef("foo")
            else
                ϕ2 = ϕ1 = SafeRef("bar")
            end
            cond2 && (ϕ2[] = x)
            return ϕ1[]
        end
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[4], r) # x
        i = findfirst(isϕ, result.ir.stmts.inst)::Int
        @test is_sroa_eligible(result.state.ssavalues[i])
        for i in findall(isnew, result.ir.stmts.inst)
            @test is_sroa_eligible(result.state.ssavalues[i])
        end
    end
    # alias via π-node
    let result = analyze_escapes((String,)) do x
            global g
            l = g
            if isa(l, SafeRef{String})
                l[] = x
            end
            nothing
        end
        @test has_all_escape(result.state.arguments[2]) # x
    end

    # dynamic semantics
    # -----------------

    # conservatively handle untyped objects
    let result = @eval analyze_escapes((Any,Any,Any,Any)) do T, x, y, z
            obj = $(Expr(:new, :T, :x, :y))
            return getfield(obj, :field1)
        end
        i = findfirst(isnew, result.ir.stmts.inst)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test #=x=# has_return_escape(result.state.arguments[3], r)
        @test #=y=# has_return_escape(result.state.arguments[4], r)
        @test #=z=# !has_return_escape(result.state.arguments[5], r)
    end
    let result = @eval analyze_escapes((Any,Any,Any,Any)) do T, x, y, z
            obj = $(Expr(:new, :T, :x))
            setfield!(obj, :field1, y)
            return getfield(obj, :field1)
        end
        i = findfirst(isnew, result.ir.stmts.inst)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test #=x=# has_return_escape(result.state.arguments[3], r)
        @test #=y=# has_return_escape(result.state.arguments[4], r)
        @test #=z=# !has_return_escape(result.state.arguments[5], r)
    end

    # conservatively handle unknown field:
    # all fields should be escaped, but the allocation itself doesn't need to be escaped
    let result = analyze_escapes((String, Symbol)) do a, fld
            obj = SafeRef(a)
            return getfield(obj, fld)
        end
        i = findfirst(isT(SafeRef{String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r) # a
        @test is_sroa_eligible(result.state.ssavalues[i]) # obj
    end
    let result = analyze_escapes((String, String, Symbol)) do a, b, fld
            obj = SafeRefs(a, b)
            return getfield(obj, fld) # should escape both `a` and `b`
        end
        i = findfirst(isT(SafeRefs{String,String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r) # a
        @test has_return_escape(result.state.arguments[3], r) # b
        @test is_sroa_eligible(result.state.ssavalues[i]) # obj
    end
    let result = analyze_escapes((String, String, Int)) do a, b, idx
            obj = SafeRefs(a, b)
            return obj[idx] # should escape both `a` and `b`
        end
        i = findfirst(isT(SafeRefs{String,String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r) # a
        @test has_return_escape(result.state.arguments[3], r) # b
        @test is_sroa_eligible(result.state.ssavalues[i]) # obj
    end
    let result = analyze_escapes((String, String, Symbol)) do a, b, fld
            obj = SafeRefs("a", "b")
            setfield!(obj, fld, a)
            return obj[2] # should escape `a`
        end
        i = findfirst(isT(SafeRefs{String,String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r) # a
        @test !has_return_escape(result.state.arguments[3], r) # b
        @test is_sroa_eligible(result.state.ssavalues[i]) # obj
    end
    let result = analyze_escapes((String, Symbol)) do a, fld
            obj = SafeRefs("a", "b")
            setfield!(obj, fld, a)
            return obj[1] # this should escape `a`
        end
        i = findfirst(isT(SafeRefs{String,String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r) # a
        @test is_sroa_eligible(result.state.ssavalues[i]) # obj
    end
    let result = analyze_escapes((String, String, Int)) do a, b, idx
            obj = SafeRefs("a", "b")
            obj[idx] = a
            return obj[2] # should escape `a`
        end
        i = findfirst(isT(SafeRefs{String,String}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r) # a
        @test !has_return_escape(result.state.arguments[3], r) # b
        @test is_sroa_eligible(result.state.ssavalues[i]) # obj
    end

    # interprocedural
    # ---------------

    let result = @eval EATModule() begin
            @noinline getx(obj) = obj[]
            $analyze_escapes((String,)) do a
                obj = SafeRef(a)
                fld = getx(obj)
                return fld
            end
        end
        i = findfirst(isnew, result.ir.stmts.inst)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r)
        # NOTE we can't scalar replace `obj`, but still we may want to stack allocate it
        @test_broken is_sroa_eligible(result.state.ssavalues[i])
    end

    # TODO interprocedural field analysis
    let result = analyze_escapes((SafeRef{String},)) do s
            s[] = "bar"
            global g = s[]
            nothing
        end
        @test_broken !has_all_escape(result.state.arguments[2])
    end

    # TODO flow-sensitivity?
    # ----------------------

    let result = analyze_escapes((Any,Any)) do a, b
            r = SafeRef{Any}(a)
            r[] = b
            return r[]
        end
        i = findfirst(isT(SafeRef{Any}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test_broken !has_return_escape(result.state.arguments[2], r) # a
        @test has_return_escape(result.state.arguments[3], r) # b
        @test is_sroa_eligible(result.state.ssavalues[i])
    end
    let result = analyze_escapes((Any,Any)) do a, b
            r = SafeRef{Any}(:init)
            r[] = a
            r[] = b
            return r[]
        end
        i = findfirst(isT(SafeRef{Any}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test_broken !has_return_escape(result.state.arguments[2], r) # a
        @test has_return_escape(result.state.arguments[3], r) # b
        @test is_sroa_eligible(result.state.ssavalues[i])
    end
    let result = analyze_escapes((Any,Any,Bool)) do a, b, cond
            r = SafeRef{Any}(:init)
            if cond
                r[] = a
                return r[]
            else
                r[] = b
                return nothing
            end
        end
        i = findfirst(isT(SafeRef{Any}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test has_return_escape(result.state.arguments[2], r) # a
        @test_broken !has_return_escape(result.state.arguments[3], r) # b
        @test is_sroa_eligible(result.state.ssavalues[i])
    end
end

# demonstrate a simple type level analysis can sometimes improve the analysis accuracy
# by compensating the lack of yet unimplemented analyses
@testset "special-casing bitstype" begin
    let result = analyze_escapes((Nothing,)) do a
            global bb = a
        end
        @test !(has_all_escape(result.state.arguments[2]))
    end

    let result = analyze_escapes((Int,)) do a
            o = SafeRef(a)
            f = o[]
            return f
        end
        i = findfirst(isT(SafeRef{Int}), result.ir.stmts.type)::Int
        r = findfirst(isreturn, result.ir.stmts.inst)::Int
        @test !has_return_escape(result.state.ssavalues[i], r)
    end

    # an escaped tuple stmt will not propagate to its Int argument (since `Int` is of bitstype)
    let result = analyze_escapes((Int,Any,)) do a, b
            t = tuple(a, b)
            return t
        end
        i = findfirst(issubT(Tuple), result.ir.stmts.type)::Int
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
    test_opt(only(methods(EscapeAnalysis.find_escapes)).sig;
        function_filter,
        # skip_nonconcrete_calls=false,
        )
    for m in methods(EscapeAnalysis.escape_builtin!)
        Base._methods_by_ftype(m.sig, 1, Base.get_world_counter()) === false && continue
        test_opt(m.sig;
            function_filter,
            # skip_nonconcrete_calls=false,
            )
    end
end

end # @testset "EscapeAnalysis" begin
