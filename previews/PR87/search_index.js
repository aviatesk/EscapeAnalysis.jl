var documenterSearchIndex = {"docs":
[{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"(Image: CI) (Image: codecov) (Image: )","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"EscapeAnalysis is a simple module that collects escape information in Julia's SSA optimization IR a.k.a. IRCode.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"You can give a try to the escape analysis with the convenience entries that EscapeAnalysis exports for testing and debugging purposes:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"EscapeAnalysis.EAUtils.code_escapes\nEscapeAnalysis.EAUtils.@code_escapes","category":"page"},{"location":"#EscapeAnalysis.EAUtils.code_escapes","page":"EscapeAnalysis","title":"EscapeAnalysis.EAUtils.code_escapes","text":"code_escapes(f, argtypes=Tuple{}; [world], [interp], [debuginfo]) -> result::EscapeResult\ncode_escapes(tt::Type{<:Tuple}; [world], [interp], [debuginfo]) -> result::EscapeResult\n\nRuns the escape analysis on optimized IR of a generic function call with the given type signature. Note that the escape analysis runs after inlining, but before any other optimizations.\n\njulia> mutable struct SafeRef{T}\n           x::T\n       end\n\njulia> Base.getindex(x::SafeRef) = x.x;\n\njulia> Base.isassigned(x::SafeRef) = true;\n\njulia> get′(x) = isassigned(x) ? x[] : throw(x);\n\njulia> result = code_escapes((String,String,String,String)) do s1, s2, s3, s4\n           r1 = Ref(s1)\n           r2 = Ref(s2)\n           r3 = SafeRef(s3)\n           try\n               s1 = get′(r1)\n               ret = sizeof(s1)\n           catch err\n               global g = err # will definitely escape `r1`\n           end\n           s2 = get′(r2)      # still `r2` doesn't escape fully\n           s3 = get′(r3)      # still `r3` doesn't escape fully\n           s4 = sizeof(s4)    # the argument `s4` doesn't escape here\n           return s2, s3, s4\n       end\n#1(X _2::String, ↑ _3::String, ↑ _4::String, ✓ _5::String) in Main at REPL[6]:2\nX  1 ── %1  = %new(Base.RefValue{String}, _2)::Base.RefValue{String}\n*′ │    %2  = %new(Base.RefValue{String}, _3)::Base.RefValue{String}\n✓′ └─── %3  = %new(SafeRef{String}, _4)::SafeRef{String}\n◌  2 ── %4  = $(Expr(:enter, #8))\n✓′ │    %5  = ϒ (%3)::SafeRef{String}\n*′ │    %6  = ϒ (%2)::Base.RefValue{String}\n✓  └─── %7  = ϒ (_5)::String\n◌  3 ── %8  = Base.isdefined(%1, :x)::Bool\n◌  └───       goto #5 if not %8\nX  4 ──       Base.getfield(%1, :x)::String\n◌  └───       goto #6\n◌  5 ──       Main.throw(%1)::Union{}\n◌  └───       unreachable\n◌  6 ──       nothing::typeof(Core.sizeof)\n◌  │          nothing::Int64\n◌  └───       $(Expr(:leave, 1))\n◌  7 ──       goto #10\n✓′ 8 ── %18 = φᶜ (%5)::SafeRef{String}\n*′ │    %19 = φᶜ (%6)::Base.RefValue{String}\n✓  │    %20 = φᶜ (%7)::String\n◌  └───       $(Expr(:leave, 1))\nX  9 ── %22 = $(Expr(:the_exception))::Any\n◌  │          (Main.g = %22)::Any\n◌  └───       $(Expr(:pop_exception, :(%4)))::Any\n✓′ 10 ┄ %25 = φ (#7 => %3, #9 => %18)::SafeRef{String}\n*′ │    %26 = φ (#7 => %2, #9 => %19)::Base.RefValue{String}\n✓  │    %27 = φ (#7 => _5, #9 => %20)::String\n◌  │    %28 = Base.isdefined(%26, :x)::Bool\n◌  └───       goto #12 if not %28\n↑  11 ─ %30 = Base.getfield(%26, :x)::String\n◌  └───       goto #13\n◌  12 ─       Main.throw(%26)::Union{}\n◌  └───       unreachable\n↑  13 ─ %34 = Base.getfield(%25, :x)::String\n◌  │    %35 = Core.sizeof::typeof(Core.sizeof)\n◌  │    %36 = (%35)(%27)::Int64\n↑  │    %37 = Core.tuple(%30, %34, %36)::Tuple{String, String, Int64}\n◌  └───       return %37\n\nThe symbols in the side of each call argument and SSA statements represents the following meaning:\n\n◌ (plain): this value is not analyzed because escape information of it won't be used anyway (when the object is isbitstype for example)\n✓ (green or cyan): this value never escapes (has_no_escape(result.state[x]) holds), colored blue if it has arg escape also (has_arg_escape(result.state[x]) holds)\n↑ (blue or yellow): this value can escape to the caller via return (has_return_escape(result.state[x]) holds), colored yellow if it has unhandled thrown escape also (has_thrown_escape(result.state[x]) holds)\nX (red): this value can escape to somewhere the escape analysis can't reason about like escapes to a global memory (has_all_escape(result.state[x]) holds)\n* (bold): this value's escape state is between the ReturnEscape and AllEscape in the partial order of EscapeInfo, colored yellow if it has unhandled thrown escape also (has_thrown_escape(result.state[x]) holds)\n′: this value has additional object field / array element information in its AliasInfo property\n\nFor testing, escape information of each call argument and SSA value can be inspected programmatically as like:\n\njulia> result.state[Core.Argument(3)]\nReturnEscape\n\njulia> result.state[Core.SSAValue(3)]\nNoEscape′\n\n\n\n\n\n","category":"function"},{"location":"#EscapeAnalysis.EAUtils.@code_escapes","page":"EscapeAnalysis","title":"EscapeAnalysis.EAUtils.@code_escapes","text":"@code_escapes [options...] f(args...)\n\nEvaluates the arguments to the function call, determines its types, and then calls code_escapes on the resulting expression. As with @code_typed and its family, any of code_escapes keyword arguments can be given as the optional arguments like @code_escapes debuginfo=:source myfunc(myargs...).\n\n\n\n\n\n","category":"macro"},{"location":"#Analysis-Design","page":"EscapeAnalysis","title":"Analysis Design","text":"","category":"section"},{"location":"#Lattice-Design","page":"EscapeAnalysis","title":"Lattice Design","text":"","category":"section"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"EscapeAnalysis is implemented as a data-flow analysis that works on a lattice of x::EscapeInfo, which is composed of the following properties:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"x.Analyzed::Bool: not formally part of the lattice, only indicates x has not been analyzed or not\nx.ReturnEscape::BitSet: records SSA statements where x can escape to the caller via return\nx.ThrownEscape::BitSet: records SSA statements where x can be thrown as exception (used for the exception handling described below)\nx.AliasInfo: maintains all possible values that can be aliased to fields or array elements of x (used for the alias analysis described below)\nx.ArgEscape::Int (not implemented yet): indicates it will escape to the caller through setfield! on argument(s)","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"These attributes can be combined to create a partial lattice that has a finite height, given the invariant that an input program has a finite number of statements, which is assured by Julia's semantics. The clever part of this lattice design is that it enables a simpler implementation of lattice operations by allowing them to handle each lattice property separately[LatticeDesign].","category":"page"},{"location":"#Backward-Escape-Propagation","page":"EscapeAnalysis","title":"Backward Escape Propagation","text":"","category":"section"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"This escape analysis implementation is based on the data-flow algorithm described in the paper[MM02]. The analysis works on the lattice of EscapeInfo and transitions lattice elements from the bottom to the top until every lattice element gets converged to a fixed point by maintaining a (conceptual) working set that contains program counters corresponding to remaining SSA statements to be analyzed. The analysis manages a single global state that tracks EscapeInfo of each argument and SSA statement, but also note that some flow-sensitivity is encoded as program counters recorded in EscapeInfo's ReturnEscape property, which can be combined with domination analysis later to reason about flow-sensitivity if necessary.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"One distinctive design of this escape analysis is that it is fully backward, i.e. escape information flows from usages to definitions. For example, in the code snippet below, EA first analyzes the statement return %1 and imposes ReturnEscape on %1 (corresponding to obj), and then it analyzes %1 = %new(Base.RefValue{String, _2})) and propagates the ReturnEscape imposed on %1 to the call argument _2 (corresponding to s):","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> code_escapes((String,)) do s\n           obj = Ref(s)\n           return obj\n       end\n#1(↑ _2::String) in Main at REPL[2]:2\n↑  1 ─ %1 = %new(Base.RefValue{String}, _2)::Base.RefValue{String}\n◌  └──      return %1","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"The key observation here is that this backward analysis allows escape information to flow naturally along the use-def chain rather than control-flow[BackandForth]. As a result this scheme enables a simple implementation of escape analysis, e.g. PhiNode for example can be handled simply by propagating escape information imposed on a PhiNode to its predecessor values:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> code_escapes((Bool, String, String)) do cnd, s, t\n           if cnd\n               obj = Ref(s)\n           else\n               obj = Ref(t)\n           end\n           return obj\n       end\n#3(✓ _2::Bool, ↑ _3::String, ↑ _4::String) in Main at REPL[3]:2\n◌  1 ─      goto #3 if not _2\n↑  2 ─ %2 = %new(Base.RefValue{String}, _3)::Base.RefValue{String}\n◌  └──      goto #4\n↑  3 ─ %4 = %new(Base.RefValue{String}, _4)::Base.RefValue{String}\n↑  4 ┄ %5 = φ (#2 => %2, #3 => %4)::Base.RefValue{String}\n◌  └──      return %5","category":"page"},{"location":"#EA-Alias-Analysis","page":"EscapeAnalysis","title":"Alias Analysis","text":"","category":"section"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"EscapeAnalysis implements a backward field analysis in order to reason about escapes imposed on object fields with certain accuracy, and x::EscapeInfo's x.AliasInfo property exists for this purpose. It records all possible values that can be aliased to fields of x at \"usage\" sites, and then the escape information of that recorded values are propagated to the actual field values later at \"definition\" sites. More specifically, the analysis records a value that may be aliased to a field of object by analyzing getfield call, and then it propagates its escape information to the field when analyzing %new(...) expression or setfield! call[Dynamism].","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> mutable struct SafeRef{T}\n           x::T\n       end\n\njulia> Base.getindex(x::SafeRef) = x.x;\n\njulia> Base.setindex!(x::SafeRef, v) = x.x = v;\n\njulia> code_escapes((String,)) do s\n           obj = SafeRef(\"init\")\n           obj[] = s\n           v = obj[]\n           return v\n       end\n#5(↑ _2::String) in Main at REPL[7]:2\n✓′ 1 ─ %1 = %new(SafeRef{String}, \"init\")::SafeRef{String}\n◌  │        Base.setfield!(%1, :x, _2)::String\n↑  │   %3 = Base.getfield(%1, :x)::String\n◌  └──      return %3","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"In the example above, ReturnEscape imposed on %3 (corresponding to v) is not directly propagated to %1 (corresponding to obj) but rather that ReturnEscape is only propagated to _2 (corresponding to s). Here %3 is recorded in %1's AliasInfo property as it can be aliased to the first field of %1, and then when analyzing Base.setfield!(%1, :x, _2)::String, that escape information is propagated to _2 but not to %1.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"So EscapeAnalysis tracks which IR elements can be aliased across a getfield-%new/setfield! chain in order to analyze escapes of object fields, but actually this alias analysis needs to be generalized to handle other IR elements as well. This is because in Julia IR the same object is sometimes represented by different IR elements and so we should make sure that those different IR elements that actually can represent the same object share the same escape information. IR elements that return the same object as their operand(s), such as PiNode and typeassert, can cause that IR-level aliasing and thus requires escape information imposed on any of such aliased values to be shared between them. More interestingly, it is also needed for correctly reasoning about mutations on PhiNode. Let's consider the following example:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> code_escapes((Bool, String,)) do cond, x\n           if cond\n               ϕ2 = ϕ1 = SafeRef(\"foo\")\n           else\n               ϕ2 = ϕ1 = SafeRef(\"bar\")\n           end\n           ϕ2[] = x\n           y = ϕ1[]\n           return y\n       end\n#7(✓ _2::Bool, ↑ _3::String) in Main at REPL[8]:2\n◌  1 ─      goto #3 if not _2\n✓′ 2 ─ %2 = %new(SafeRef{String}, \"foo\")::SafeRef{String}\n◌  └──      goto #4\n✓′ 3 ─ %4 = %new(SafeRef{String}, \"bar\")::SafeRef{String}\n✓′ 4 ┄ %5 = φ (#2 => %2, #3 => %4)::SafeRef{String}\n✓′ │   %6 = φ (#2 => %2, #3 => %4)::SafeRef{String}\n◌  │        Base.setfield!(%5, :x, _3)::String\n↑  │   %8 = Base.getfield(%6, :x)::String\n◌  └──      return %8","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"ϕ1 = %5 and ϕ2 = %6 are aliased and thus ReturnEscape imposed on %8 = Base.getfield(%6, :x)::String (corresponding to y = ϕ1[]) needs to be propagated to Base.setfield!(%5, :x, _3)::String (corresponding to ϕ2[] = x). In order for such escape information to be propagated correctly, the analysis should recognize that the predecessors of ϕ1 and ϕ2 can be aliased as well and equalize their escape information.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"One interesting property of such aliasing information is that it is not known at \"usage\" site but can only be derived at \"definition\" site (as aliasing is conceptually equivalent to assignment), and thus it doesn't naturally fit in a backward analysis. In order to efficiently propagate escape information between related values, EscapeAnalysis.jl uses an approach inspired by the escape analysis algorithm explained in an old JVM paper[JVM05]. That is, in addition to managing escape lattice elements, the analysis also maintains an \"equi\"-alias set, a disjoint set of aliased arguments and SSA statements. The alias set manages values that can be aliased to each other and allows escape information imposed on any of such aliased values to be equalized between them.","category":"page"},{"location":"#EA-Array-Analysis","page":"EscapeAnalysis","title":"Array Analysis","text":"","category":"section"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"The alias analysis for object fields described above can also be generalized to analyze array operations. EscapeAnalysis implements handlings for various primitive array operations so that it can propagate escapes via arrayref-arrayset use-def chain and does not escape allocated arrays too conservatively:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> code_escapes((String,)) do s\n           ary = Any[]\n           push!(ary, SafeRef(s))\n           return ary[1], length(ary)\n       end\n#9(↑ _2::String) in Main at REPL[9]:2\n*′ 1 ── %1  = $(Expr(:foreigncall, :(:jl_alloc_array_1d), Vector{Any}, svec(Any, Int64), 0, :(:ccall), Vector{Any}, 0, 0))::Vector{Any}\n↑  │    %2  = %new(SafeRef{String}, _2)::SafeRef{String}\n◌  │    %3  = Core.lshr_int(1, 63)::Int64\n◌  │    %4  = Core.trunc_int(Core.UInt8, %3)::UInt8\n◌  │    %5  = Core.eq_int(%4, 0x01)::Bool\n◌  └───       goto #3 if not %5\n◌  2 ──       invoke Core.throw_inexacterror(:check_top_bit::Symbol, UInt64::Type{UInt64}, 1::Int64)::Union{}\n◌  └───       unreachable\n◌  3 ──       goto #4\n◌  4 ── %10 = Core.bitcast(Core.UInt64, 1)::UInt64\n◌  └───       goto #5\n◌  5 ──       goto #6\n◌  6 ──       goto #7\n◌  7 ──       goto #8\n◌  8 ──       $(Expr(:foreigncall, :(:jl_array_grow_end), Nothing, svec(Any, UInt64), 0, :(:ccall), :(%1), :(%10), :(%10)))::Nothing\n◌  └───       goto #9\n◌  9 ── %17 = Base.arraylen(%1)::Int64\n◌  │          Base.arrayset(true, %1, %2, %17)::Vector{Any}\n◌  └───       goto #10\n↑  10 ─ %20 = Base.arrayref(true, %1, 1)::Any\n◌  │    %21 = Base.arraylen(%1)::Int64\n↑  │    %22 = Core.tuple(%20, %21)::Tuple{Any, Int64}\n◌  └───       return %22","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"In the above example EscapeAnalysis understands that %20 and %2 (corresponding to the allocated object SafeRef(s)) are aliased via the arrayset-arrayref chain and imposes ReturnEscape on them, but not impose it on the allocated array %1 (corresponding to ary). EscapeAnalysis still imposes ThrownEscape on ary since it also needs to account for potential escapes via BoundsError, but also note that such unhandled ThrownEscape can often be ignored when optimizing the ary allocation.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"Furthermore, in cases when array index information as well as array dimensions can be known precisely, EscapeAnalysis is able to even reason about \"per-element\" aliasing via arrayref-arrayset chain, as EscapeAnalysis does \"per-field\" alias analysis for objects:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> code_escapes((String,String)) do s, t\n           ary = Vector{Any}(undef, 2)\n           ary[1] = SafeRef(s)\n           ary[2] = SafeRef(t)\n           return ary[1], length(ary)\n       end\n#11(↑ _2::String, * _3::String) in Main at REPL[10]:2\n*′ 1 ─ %1 = $(Expr(:foreigncall, :(:jl_alloc_array_1d), Vector{Any}, svec(Any, Int64), 0, :(:ccall), Vector{Any}, 2, 2))::Vector{Any}\n↑  │   %2 = %new(SafeRef{String}, _2)::SafeRef{String}\n◌  │        Base.arrayset(true, %1, %2, 1)::Vector{Any}\n*  │   %4 = %new(SafeRef{String}, _3)::SafeRef{String}\n◌  │        Base.arrayset(true, %1, %4, 2)::Vector{Any}\n↑  │   %6 = Base.arrayref(true, %1, 1)::Any\n◌  │   %7 = Base.arraylen(%1)::Int64\n↑  │   %8 = Core.tuple(%6, %7)::Tuple{Any, Int64}\n◌  └──      return %8","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"Note that ReturnEscape is only imposed on %2 (corresponding to SafeRef(s)) but not on %4 (corresponding to SafeRef(t)). This is because the allocated array's dimension and indices involved with all arrayref/arrayset operations are available as constant information and EscapeAnalysis can understand that %6 is aliased to %2 but never be aliased to %4. In this kind of case, the succeeding optimization passes will be able to replace Base.arrayref(true, %1, 1)::Any with %2 (a.k.a. \"load-forwarding\") and eventually eliminate the allocation of array %1 entirely (a.k.a. \"scalar-replacement\").","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"When compared to object field analysis, where an access to object field can be analyzed trivially using type information derived by inference, array dimension isn't encoded as type information and so we need an additional analysis to derive that information. EscapeAnalysis at this moment first does an additional simple linear scan to analyze dimensions of allocated arrays before firing up the main analysis routine so that the succeeding escape analysis can precisely analyze operations on those arrays.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"However, such precise \"per-element\" alias analyis is often hard. Essentially, the main difficulty inherit to array is that array dimension and index are often non-constant:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"loop often produces loop-variant, non-constant array indices\n(specific to vectors) array resizing changes array dimension and invalidates its constant-ness","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"Let's discuss those difficulties with concrete examples.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"In the following example, EscapeAnalysis fails the precise alias analysis since the index at the Base.arrayset(false, %4, %8, %6)::Vector{Any} is not (trivially) constant. Especially Any[nothing, nothing] forms a loop and calls that arrayset operation in a loop, where %6 is represented as a ϕ-node value (whose value is control-flow dependent). As a result, ReturnEscape ends up imposed on both %23 (corresponding to SafeRef(s)) and %25 (corresponding to SafeRef(t)), although ideally we want it to be imposed only on %23 but not on %25:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> code_escapes((String,String)) do s, t\n           ary = Any[nothing, nothing]\n           ary[1] = SafeRef(s)\n           ary[2] = SafeRef(t)\n           return ary[1], length(ary)\n       end\n#13(↑ _2::String, ↑ _3::String) in Main at REPL[11]:2\n◌  1 ─ %1  = Main.nothing::Core.Const(nothing)\n◌  │   %2  = Main.nothing::Core.Const(nothing)\n◌  │   %3  = Core.tuple(%1, %2)::Core.Const((nothing, nothing))\n*′ │   %4  = $(Expr(:foreigncall, :(:jl_alloc_array_1d), Vector{Any}, svec(Any, Int64), 0, :(:ccall), Vector{Any}, 2, 2))::Vector{Any}\n◌  └──       goto #7 if not true\n◌  2 ┄ %6  = φ (#1 => 1, #6 => %16)::Int64\n◌  │   %7  = φ (#1 => 1, #6 => %17)::Int64\n↑  │   %8  = Base.getfield(%3, %6, false)::Nothing\n◌  │         Base.arrayset(false, %4, %8, %6)::Vector{Any}\n◌  │   %10 = (%7 === 2)::Bool\n◌  └──       goto #4 if not %10\n◌  3 ─       Base.nothing::Nothing\n◌  └──       goto #5\n◌  4 ─ %14 = Base.add_int(%7, 1)::Int64\n◌  └──       goto #5\n◌  5 ┄ %16 = φ (#4 => %14)::Int64\n◌  │   %17 = φ (#4 => %14)::Int64\n◌  │   %18 = φ (#3 => true, #4 => false)::Bool\n◌  │   %19 = Base.not_int(%18)::Bool\n◌  └──       goto #7 if not %19\n◌  6 ─       goto #2\n◌  7 ┄       goto #8\n↑  8 ─ %23 = %new(SafeRef{String}, _2)::SafeRef{String}\n◌  │         Base.arrayset(true, %4, %23, 1)::Vector{Any}\n↑  │   %25 = %new(SafeRef{String}, _3)::SafeRef{String}\n◌  │         Base.arrayset(true, %4, %25, 2)::Vector{Any}\n↑  │   %27 = Base.arrayref(true, %4, 1)::Any\n◌  │   %28 = Base.arraylen(%4)::Int64\n↑  │   %29 = Core.tuple(%27, %28)::Tuple{Any, Int64}\n◌  └──       return %29","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"The next example illustrates how vector resizing makes precise alias analysis hard. The essential difficulty is that the dimension of allocated array %1 is first initialized as 0, but it changes by the two :jl_array_grow_end calls afterwards. EscapeAnalysis currently simply gives up precise alias analysis whenever it encounters any array resizing operations and so ReturnEscape is imposed on both %2 (corresponding to SafeRef(s)) and %20 (corresponding to SafeRef(t)):","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> code_escapes((String,String)) do s, t\n           ary = Any[]\n           push!(ary, SafeRef(s))\n           push!(ary, SafeRef(t))\n           ary[1], length(ary)\n       end\n#15(↑ _2::String, ↑ _3::String) in Main at REPL[12]:2\n*′ 1 ── %1  = $(Expr(:foreigncall, :(:jl_alloc_array_1d), Vector{Any}, svec(Any, Int64), 0, :(:ccall), Vector{Any}, 0, 0))::Vector{Any}\n↑  │    %2  = %new(SafeRef{String}, _2)::SafeRef{String}\n◌  │    %3  = Core.lshr_int(1, 63)::Int64\n◌  │    %4  = Core.trunc_int(Core.UInt8, %3)::UInt8\n◌  │    %5  = Core.eq_int(%4, 0x01)::Bool\n◌  └───       goto #3 if not %5\n◌  2 ──       invoke Core.throw_inexacterror(:check_top_bit::Symbol, UInt64::Type{UInt64}, 1::Int64)::Union{}\n◌  └───       unreachable\n◌  3 ──       goto #4\n◌  4 ── %10 = Core.bitcast(Core.UInt64, 1)::UInt64\n◌  └───       goto #5\n◌  5 ──       goto #6\n◌  6 ──       goto #7\n◌  7 ──       goto #8\n◌  8 ──       $(Expr(:foreigncall, :(:jl_array_grow_end), Nothing, svec(Any, UInt64), 0, :(:ccall), :(%1), :(%10), :(%10)))::Nothing\n◌  └───       goto #9\n◌  9 ── %17 = Base.arraylen(%1)::Int64\n◌  │          Base.arrayset(true, %1, %2, %17)::Vector{Any}\n◌  └───       goto #10\n↑  10 ─ %20 = %new(SafeRef{String}, _3)::SafeRef{String}\n◌  │    %21 = Core.lshr_int(1, 63)::Int64\n◌  │    %22 = Core.trunc_int(Core.UInt8, %21)::UInt8\n◌  │    %23 = Core.eq_int(%22, 0x01)::Bool\n◌  └───       goto #12 if not %23\n◌  11 ─       invoke Core.throw_inexacterror(:check_top_bit::Symbol, UInt64::Type{UInt64}, 1::Int64)::Union{}\n◌  └───       unreachable\n◌  12 ─       goto #13\n◌  13 ─ %28 = Core.bitcast(Core.UInt64, 1)::UInt64\n◌  └───       goto #14\n◌  14 ─       goto #15\n◌  15 ─       goto #16\n◌  16 ─       goto #17\n◌  17 ─       $(Expr(:foreigncall, :(:jl_array_grow_end), Nothing, svec(Any, UInt64), 0, :(:ccall), :(%1), :(%28), :(%28)))::Nothing\n◌  └───       goto #18\n◌  18 ─ %35 = Base.arraylen(%1)::Int64\n◌  │          Base.arrayset(true, %1, %20, %35)::Vector{Any}\n◌  └───       goto #19\n↑  19 ─ %38 = Base.arrayref(true, %1, 1)::Any\n◌  │    %39 = Base.arraylen(%1)::Int64\n↑  │    %40 = Core.tuple(%38, %39)::Tuple{Any, Int64}\n◌  └───       return %40","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"In order to address these difficulties, we need inference to be aware of array dimensions and propagate array dimenstions in a flow-sensitive way[ArrayDimension], as well as come up with nice representation of loop-variant values.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"EscapeAnalysis at this moment quickly switches to the more imprecise analysis that doesn't track precise index information in cases when array dimensions or indices are trivially non constant. The switch can naturally be implemented as a lattice join operation of EscapeInfo.AliasInfo property in the data-flow analysis framework.","category":"page"},{"location":"#EA-Exception-Handling","page":"EscapeAnalysis","title":"Exception Handling","text":"","category":"section"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"It would be also worth noting how EscapeAnalysis handles possible escapes via exceptions. Naively it seems enough to propagate escape information imposed on :the_exception object to all values that may be thrown in a corresponding try block. But there are actually several other ways to access to the exception object in Julia, such as Base.current_exceptions and manual catch of rethrown object. For example, escape analysis needs to account for potential escape of r in the example below:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> const Gx = Ref{Any}();\n\njulia> @noinline function rethrow_escape!()\n           try\n               rethrow()\n           catch err\n               Gx[] = err\n           end\n       end;\n\njulia> get′(x) = isassigned(x) ? x[] : throw(x);\n\njulia> code_escapes() do\n           r = Ref{String}()\n           local t\n           try\n               t = get′(r)\n           catch err\n               t = typeof(err)   # `err` (which `r` aliases to) doesn't escape here\n               rethrow_escape!() # but `r` escapes here\n           end\n           return t\n       end\n#17() in Main at REPL[16]:2\nX  1 ── %1  = %new(Base.RefValue{String})::Base.RefValue{String}\n◌  2 ── %2  = $(Expr(:enter, #8))\n◌  3 ── %3  = Base.isdefined(%1, :x)::Bool\n◌  └───       goto #5 if not %3\n↑  4 ── %5  = Base.getfield(%1, :x)::String\n◌  └───       goto #6\n◌  5 ──       Main.throw(%1)::Union{}\n◌  └───       unreachable\n◌  6 ──       $(Expr(:leave, 1))\n◌  7 ──       goto #10\n◌  8 ──       $(Expr(:leave, 1))\n✓  9 ── %12 = $(Expr(:the_exception))::Any\n↑  │    %13 = Main.typeof(%12)::DataType\n◌  │          invoke Main.rethrow_escape!()::Any\n◌  └───       $(Expr(:pop_exception, :(%2)))::Any\n↑  10 ┄ %16 = φ (#7 => %5, #9 => %13)::Union{DataType, String}\n◌  └───       return %16","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"It requires a global analysis in order to correctly reason about all possible escapes via existing exception interfaces. For now we always propagate the topmost escape information to all potentially thrown objects conservatively, since such an additional analysis might not be worthwhile to do given that exception handling and error path usually don't need to be very performance sensitive, and also optimizations of error paths might be very ineffective anyway since they are often even \"unoptimized\" intentionally for latency reasons.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"x::EscapeInfo's x.ThrownEscape property records SSA statements where x can be thrown as an exception. Using this information EscapeAnalysis can propagate possible escapes via exceptions limitedly to only those may be thrown in each try region:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> result = code_escapes((String,String)) do s1, s2\n           r1 = Ref(s1)\n           r2 = Ref(s2)\n           local ret\n           try\n               s1 = get′(r1)\n               ret = sizeof(s1)\n           catch err\n               global g = err # will definitely escape `r1`\n           end\n           s2 = get′(r2)      # still `r2` doesn't escape fully\n           return s2\n       end\n#19(X _2::String, ↑ _3::String) in Main at REPL[17]:2\nX  1 ── %1  = %new(Base.RefValue{String}, _2)::Base.RefValue{String}\n*′ └─── %2  = %new(Base.RefValue{String}, _3)::Base.RefValue{String}\n◌  2 ── %3  = $(Expr(:enter, #8))\n*′ └─── %4  = ϒ (%2)::Base.RefValue{String}\n◌  3 ── %5  = Base.isdefined(%1, :x)::Bool\n◌  └───       goto #5 if not %5\nX  4 ──       Base.getfield(%1, :x)::String\n◌  └───       goto #6\n◌  5 ──       Main.throw(%1)::Union{}\n◌  └───       unreachable\n◌  6 ──       nothing::typeof(Core.sizeof)\n◌  │          nothing::Int64\n◌  └───       $(Expr(:leave, 1))\n◌  7 ──       goto #10\n*′ 8 ── %15 = φᶜ (%4)::Base.RefValue{String}\n◌  └───       $(Expr(:leave, 1))\nX  9 ── %17 = $(Expr(:the_exception))::Any\n◌  │          (Main.g = %17)::Any\n◌  └───       $(Expr(:pop_exception, :(%3)))::Any\n*′ 10 ┄ %20 = φ (#7 => %2, #9 => %15)::Base.RefValue{String}\n◌  │    %21 = Base.isdefined(%20, :x)::Bool\n◌  └───       goto #12 if not %21\n↑  11 ─ %23 = Base.getfield(%20, :x)::String\n◌  └───       goto #13\n◌  12 ─       Main.throw(%20)::Union{}\n◌  └───       unreachable\n◌  13 ─       return %23","category":"page"},{"location":"#Analysis-Usage","page":"EscapeAnalysis","title":"Analysis Usage","text":"","category":"section"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"When using EscapeAnalysis in Julia's high-level compilation pipeline, we can run analyze_escapes(ir::IRCode) -> estate::EscapeState to analyze escape information of each SSA-IR element in ir.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"Note that it should be most effective if analyze_escapes runs after inlining, as EscapeAnalysis's interprocedural escape information handling is limited at this moment.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"Since the computational cost of analyze_escapes is not that cheap, it is more ideal if it runs once and succeeding optimization passes incrementally update     the escape information upon IR transformation.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"EscapeAnalysis.analyze_escapes\nEscapeAnalysis.EscapeState\nEscapeAnalysis.EscapeInfo\nEscapeAnalysis.cache_escapes!","category":"page"},{"location":"#EscapeAnalysis.analyze_escapes","page":"EscapeAnalysis","title":"EscapeAnalysis.analyze_escapes","text":"analyze_escapes(ir::IRCode, nargs::Int) -> estate::EscapeState\n\nAnalyzes escape information in ir. nargs is the number of actual arguments of the analyzed call.\n\n\n\n\n\n","category":"function"},{"location":"#EscapeAnalysis.EscapeState","page":"EscapeAnalysis","title":"EscapeAnalysis.EscapeState","text":"estate::EscapeState\n\nExtended lattice that maps arguments and SSA values to escape information represented as EscapeInfo. Escape information imposed on SSA IR element x can be retrieved by estate[x].\n\n\n\n\n\n","category":"type"},{"location":"#EscapeAnalysis.EscapeInfo","page":"EscapeAnalysis","title":"EscapeAnalysis.EscapeInfo","text":"x::EscapeInfo\n\nA lattice for escape information, which holds the following properties:\n\nx.Analyzed::Bool: not formally part of the lattice, only indicates x has not been analyzed or not\nx.ReturnEscape::Bool: indicates x can escape to the caller via return\nx.ThrownEscape::BitSet: records SSA statements numbers where x can be thrown as exception:\nisempty(x.ThrownEscape): x will never be thrown in this call frame (the bottom)\npc ∈ x.ThrownEscape: x may be thrown at the SSA statement at pc\n-1 ∈ x.ThrownEscape: x may be thrown at arbitrary points of this call frame (the top)\nThis information will be used by escape_exception! to propagate potential escapes via exception.\nx.AliasInfo::Union{IndexableFields,Unindexable,Bool}: maintains all possible values that can be aliased to fields or array elements of x:\nx.AliasInfo === false indicates the fields/elements of x isn't analyzed yet\nx.AliasInfo === true indicates the fields/elements of x can't be analyzed, e.g. the type of x is not known or is not concrete and thus its fields/elements can't be known precisely\nx.AliasInfo::IndexableFields records all the possible values that can be aliased to fields of object x with precise index information\nx.AliasInfo::IndexableElements records all the possible values that can be aliased to elements of array x with precise index information\nx.AliasInfo::Unindexable records all the possible values that can be aliased to fields/elements of x without precise index information\nx.Liveness::BitSet: records SSA statement numbers where x should be live, e.g. to be used as a call argument, to be returned to a caller, or preserved for :foreigncall:\nisempty(x.Liveness): x is never be used in this call frame (the bottom)\n0 ∈ x.Liveness also has the special meaning that it's a call argument of the currently analyzed call frame (and thus it's visible from the caller immediately).\npc ∈ x.Liveness: x may be used at the SSA statement at pc\n-1 ∈ x.Liveness: x may be used at arbitrary points of this call frame (the top)\nx.ArgEscape::Int (not implemented yet): indicates it will escape to the caller through setfield! on argument(s)\n-1 : no escape\n0 : unknown or multiple\nn : through argument N\n\nThere are utility constructors to create common EscapeInfos, e.g.,\n\nNoEscape(): the bottom(-like) element of this lattice, meaning it won't escape to anywhere\nAllEscape(): the topmost element of this lattice, meaning it will escape to everywhere\n\nanalyze_escapes will transition these elements from the bottom to the top, in the same direction as Julia's native type inference routine. An abstract state will be initialized with the bottom(-like) elements:\n\nthe call arguments are initialized as ArgEscape(), whose Liveness property includes 0 to indicate that it is passed as a call argument and visible from a caller immediately\nthe other states are initialized as NotAnalyzed(), which is a special lattice element that is slightly lower than NoEscape, but at the same time doesn't represent any meaning other than it's not analyzed yet (thus it's not formally part of the lattice)\n\n\n\n\n\n","category":"type"},{"location":"#EscapeAnalysis.cache_escapes!","page":"EscapeAnalysis","title":"EscapeAnalysis.cache_escapes!","text":"cache_escapes!(linfo::MethodInstance, estate::EscapeState, _::IRCode)\n\nTransforms escape information of estate for interprocedural propagation, and caches it in a global cache that can then be looked up later when linfo callsite is seen again.\n\n\n\n\n\n","category":"function"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"[LatticeDesign]: Our type inference implementation takes the alternative approach, where each lattice property is represented by a special lattice element type object. It turns out that it started to complicate implementations of the lattice operations mainly because it often requires conversion rules between each lattice element type object. And we are working on overhauling our type inference lattice implementation with EscapeInfo-like lattice design.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"[MM02]: A Graph-Free approach to Data-Flow Analysis.      Markas Mohnen, 2002, April.      https://api.semanticscholar.org/CorpusID:28519618.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"[BackandForth]: Our type inference algorithm in contrast is implemented as a forward analysis, because type information usually flows from \"definition\" to \"usage\" and it is more natural and effective to propagate such information in a forward way.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"[Dynamism]: In some cases, however, object fields can't be analyzed precisely. For example, object may escape to somewhere EscapeAnalysis can't account for possible memory effects on it, or fields of the objects simply can't be known because of the lack of type information. In such cases AliasInfo property is raised to the topmost element within its own lattice order, and it causes succeeding field analysis to be conservative and escape information imposed on fields of an unanalyzable object to be propagated to the object itself.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"[JVM05]: Escape Analysis in the Context of Dynamic Compilation and Deoptimization.       Thomas Kotzmann and Hanspeter Mössenböck, 2005, June.       https://dl.acm.org/doi/10.1145/1064979.1064996.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"[ArrayDimension]: Otherwise we will need yet another forward data-flow analysis on top of the escape analysis.","category":"page"}]
}
