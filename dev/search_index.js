var documenterSearchIndex = {"docs":
[{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"(Image: CI) (Image: codecov) (Image: )","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"EscapeAnalysis is a simple module that collects escape information in Julia's SSA optimization IR a.k.a. IRCode.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"You can give a try to the escape analysis with the convenience entries that EscapeAnalysis exports for testing and debugging purposes:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"EscapeAnalysis.EAUtils.code_escapes\nEscapeAnalysis.EAUtils.@code_escapes","category":"page"},{"location":"#EscapeAnalysis.EAUtils.code_escapes","page":"EscapeAnalysis","title":"EscapeAnalysis.EAUtils.code_escapes","text":"code_escapes(f, argtypes=Tuple{}; [world], [interp]) -> result::EscapeResult\ncode_escapes(tt::Type{<:Tuple}; [world], [interp]) -> result::EscapeResult\n\nRuns the escape analysis on optimized IR of a genefic function call with the given type signature. Note that the escape analysis runs after inlining, but before any other optimizations.\n\njulia> mutable struct SafeRef{T}\n           x::T\n       end\n\njulia> Base.getindex(x::SafeRef) = x.x;\n\njulia> Base.isassigned(x::SafeRef) = true;\n\njulia> get′(x) = isassigned(x) ? x[] : throw(x);\n\njulia> result = code_escapes((String,String,String)) do s1, s2, s3\n           r1 = Ref(s1)\n           r2 = Ref(s2)\n           r3 = SafeRef(s3)\n           try\n               s1 = get′(r1)\n               ret = sizeof(s1)\n           catch err\n               global g = err # will definitely escape `r1`\n           end\n           s2 = get′(r2)      # still `r2` doesn't escape fully\n           s3 = get′(r3)      # still `r2` doesn't escape fully\n           return s2, s3\n       end\n#3(X _2::String, ↑ _3::String, ↑ _4::String) in Main at REPL[7]:2\n2  X  1 ── %1  = %new(Base.RefValue{String}, _2)::Base.RefValue{String}   │╻╷╷ Ref\n3  *′ │    %2  = %new(Base.RefValue{String}, _3)::Base.RefValue{String}   │╻╷╷ Ref\n4  ✓′ └─── %3  = %new(SafeRef{String}, _4)::SafeRef{String}               │╻╷  SafeRef\n5  ◌  2 ── %4  = $(Expr(:enter, #8))                                      │\n   ✓′ │    %5  = ϒ (%3)::SafeRef{String}                                  │\n   *′ └─── %6  = ϒ (%2)::Base.RefValue{String}                            │\n6  ◌  3 ── %7  = Base.isdefined(%1, :x)::Bool                             │╻╷  get′\n   ◌  └───       goto #5 if not %7                                        ││\n   X  4 ──       Base.getfield(%1, :x)::String                            ││╻   getindex\n   ◌  └───       goto #6                                                  ││\n   ◌  5 ──       Main.throw(%1)::Union{}                                  ││\n   ◌  └───       unreachable                                              ││\n7  ◌  6 ──       nothing::typeof(Core.sizeof)                             │╻   sizeof\n   ◌  │          nothing::Int64                                           ││\n   ◌  └───       $(Expr(:leave, 1))                                       │\n   ◌  7 ──       goto #10                                                 │\n   ✓′ 8 ── %17 = φᶜ (%5)::SafeRef{String}                                 │\n   *′ │    %18 = φᶜ (%6)::Base.RefValue{String}                           │\n   ◌  └───       $(Expr(:leave, 1))                                       │\n   X  9 ── %20 = $(Expr(:the_exception))::Any                             │\n9  ◌  │          (Main.g = %20)::Any                                      │\n   ◌  └───       $(Expr(:pop_exception, :(%4)))::Any                      │\n11 ✓′ 10 ┄ %23 = φ (#7 => %3, #9 => %17)::SafeRef{String}                 │\n   *′ │    %24 = φ (#7 => %2, #9 => %18)::Base.RefValue{String}           │\n   ◌  │    %25 = Base.isdefined(%24, :x)::Bool                            ││╻   isassigned\n   ◌  └───       goto #12 if not %25                                      ││\n   ↑  11 ─ %27 = Base.getfield(%24, :x)::String                           │││╻   getproperty\n   ◌  └───       goto #13                                                 ││\n   ◌  12 ─       Main.throw(%24)::Union{}                                 ││\n   ◌  └───       unreachable                                              ││\n12 ↑  13 ─ %31 = Base.getfield(%23, :x)::String                           │╻╷╷ get′\n13 ↑  │    %32 = Core.tuple(%27, %31)::Tuple{String, String}              │\n   ◌  └───       return %32                                               │\n\nThe symbols in the side of each call argument and SSA statements represents the following meaning:\n\n◌: this value is not analyzed because escape information of it won't be used anyway (when the object is isbitstype for example)\n✓: this value never escapes (has_no_escape(result.state[x]) holds)\n↑: this value can escape to the caller via return (has_return_escape(result.state[x]) holds)\nX: this value can escape to somewhere the escape analysis can't reason about like escapes to a global memory (has_all_escape(result.state[x]) holds)\n*: this value's escape state is between the ReturnEscape and AllEscape in the EscapeLattice, e.g. it has unhandled ThrownEscape\n\nand additional ′ indicates that field analysis has been done successfully on that value.\n\nFor testing, escape information of each call argument and SSA value can be inspected programmatically as like:\n\njulia> result.state[Core.Argument(3)]\nReturnEscape\n\njulia> result.state[Core.SSAValue(3)]\nNoEscape′\n\n\n\n\n\n","category":"function"},{"location":"#EscapeAnalysis.EAUtils.@code_escapes","page":"EscapeAnalysis","title":"EscapeAnalysis.EAUtils.@code_escapes","text":"@code_escapes [options...] f(args...)\n\nEvaluates the arguments to the function call, determines its types, and then calls code_escapes on the resulting expression. As with @code_typed and its family, any of code_escapes keyword arguments can be given as the optional arguments like @code_escpase interp=myinterp myfunc(myargs...).\n\n\n\n\n\n","category":"macro"},{"location":"#Analysis-Design","page":"EscapeAnalysis","title":"Analysis Design","text":"","category":"section"},{"location":"#Lattice-Design","page":"EscapeAnalysis","title":"Lattice Design","text":"","category":"section"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"EscapeAnalysis is implemented as a data-flow analysis that works on a lattice called x::EscapeLattice, which is composed of the following properties:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"x.Analyzed::Bool: not formally part of the lattice, only indicates x has not been analyzed or not\nx.ReturnEscape::BitSet: records SSA statements where x can escape to the caller via return\nx.ThrownEscape::BitSet: records SSA statements where x can be thrown as exception (used for the exception handling described below)\nx.AliasEscapes: maintains all possible values that can be aliased to fields or array elements of x (used for the alias analysis described below)\nx.ArgEscape::Int (not implemented yet): indicates it will escape to the caller through setfield! on argument(s)","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"These attributes can be combined to create a partial lattice that has a finite height, given the invariant that an input program has a finite number of statements, which is assured by Julia's semantics. The clever part of this lattice design is that it enables a simpler implementation of lattice operations by allowing them to handle each lattice property separately[LatticeDesign].","category":"page"},{"location":"#Backward-Escape-Propagation","page":"EscapeAnalysis","title":"Backward Escape Propagation","text":"","category":"section"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"This escape analysis implementation is based on the data-flow algorithm described in the paper[MM02]. The analysis works on the lattice of EscapeLattice and transitions lattice elements from the bottom to the top until every lattice element gets converged to a fixed point by maintaining a (conceptual) working set that contains program counters corresponding to remaining SSA statements to be analyzed. The analysis manages a single global state that tracks EscapeLattice of each argument and SSA statement, but also note that some flow-sensitivity is encoded as program counters recorded in EscapeLattice's ReturnEscape property, which can be combined with domination analysis later to reason about flow-sensitivity if necessary.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"One distinctive design of this escape analysis is that it is fully backward, i.e. escape information flows from usages to definitions. For example, in the code snippet below, EA first analyzes the statement return %1 and imposes ReturnEscape on %1 (corresponding to obj), and then it analyzes %1 = %new(Base.RefValue{String, _2})) and propagates the ReturnEscape imposed on %1 to the call argument _2 (corresponding to s):","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> code_escapes((String,)) do s\n           obj = Ref(s)\n           return obj\n       end\n#1(↑ _2::String) in Main at REPL[2]:2\n2 ↑  1 ─ %1 = %new(Base.RefValue{String}, _2)::Base.RefValue{String}                │╻╷╷ Ref\n3 ◌  └──      return %1                                                             │","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"The key observation here is that this backward analysis allows escape information to flow naturally along the use-def chain rather than control-flow[BackandForth]. As a result this scheme enables a simple implementation of escape analysis, e.g. PhiNode for example can be handled simply by propagating escape information imposed on a PhiNode to its predecessor values:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> code_escapes((Bool, String, String)) do cnd, s, t\n           if cnd\n               obj = Ref(s)\n           else\n               obj = Ref(t)\n           end\n           return obj\n       end\n  #3(↑ _2::Bool, ↑ _3::String, ↑ _4::String) in Main at REPL[3]:2\n2 ◌  1 ─      goto #3 if not _2                                                     │\n3 ↑  2 ─ %2 = %new(Base.RefValue{String}, _3)::Base.RefValue{String}                │╻╷╷ Ref\n  ◌  └──      goto #4                                                               │\n5 ↑  3 ─ %4 = %new(Base.RefValue{String}, _4)::Base.RefValue{String}                │╻╷╷ Ref\n7 ↑  4 ┄ %5 = φ (#2 => %2, #3 => %4)::Base.RefValue{String}                         │\n  ◌  └──      return %5                                                             │","category":"page"},{"location":"#Alias-Analysis","page":"EscapeAnalysis","title":"Alias Analysis","text":"","category":"section"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"EscapeAnalysis implements a backward field analysis in order to reason about escapes imposed on object fields with certain accuracy, and x::EscapeLattice's x.AliasEscapes property exists for this purpose. It records all possible values that can be aliased to fields of x at \"usage\" sites, and then the escape information of that recorded values are propagated to the actual field values later at \"definition\" sites. More specifically, the analysis records a value that may be aliased to a field of object by analyzing getfield call, and then it propagates its escape information to the field when analyzing %new(...) expression or setfield! call[Dynamism].","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> mutable struct SafeRef{T}\n           x::T\n       end\n\njulia> Base.getindex(x::SafeRef) = x.x;\n\njulia> Base.setindex!(x::SafeRef, v) = x.x = v;\n\njulia> code_escapes((String,)) do s\n           obj = SafeRef(\"init\")\n           obj[] = s\n           v = obj[]\n           return v\n       end\n#5(↑ _2::String) in Main at REPL[7]:2\n2 ✓′ 1 ─ %1 = %new(SafeRef{String}, \"init\")::SafeRef{String}                   │╻╷ SafeRef\n3 ◌  │        Base.setfield!(%1, :x, _2)::String                               │╻╷ setindex!\n4 ↑  │   %3 = Base.getfield(%1, :x)::String                                    │╻╷ getindex\n5 ◌  └──      return %3                                                        │","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"In the example above, ReturnEscape imposed on %3 (corresponding to v) is not directly propagated to %1 (corresponding to obj) but rather that ReturnEscape is only propagated to _2 (corresponding to s). Here %3 is recorded in %1's AliasEscapes property as it can be aliased to the first field of %1, and then when analyzing Base.setfield!(%1, :x, _2)::String, that escape information is propagated to _2 but not to %1.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"So EscapeAnalysis tracks which IR elements can be aliased across a getfield-%new/setfield! chain in order to analyze escapes of object fields, but actually this alias analysis needs to be generalized to handle other IR elements as well. This is because in Julia IR the same object is sometimes represented by different IR elements and so we should make sure that those different IR elements that actually can represent the same object share the same escape information. IR elements that return the same object as their operand(s), such as PiNode and typeassert, can cause that IR-level aliasing and thus requires escape information imposed on any of such aliased values to be shared between them. More interestingly, it is also needed for correctly reasoning about mutations on PhiNode. Let's consider the following example:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> code_escapes((Bool, String,)) do cond, x\n           if cond\n               ϕ2 = ϕ1 = SafeRef(\"foo\")\n           else\n               ϕ2 = ϕ1 = SafeRef(\"bar\")\n           end\n           ϕ2[] = x\n           y = ϕ1[]\n           return y\n       end\n#7(↑ _2::Bool, ↑ _3::String) in Main at REPL[8]:2\n2 ◌  1 ─      goto #3 if not _2                                                │\n3 ✓′ 2 ─ %2 = %new(SafeRef{String}, \"foo\")::SafeRef{String}                    │╻╷ SafeRef\n  ◌  └──      goto #4                                                          │\n5 ✓′ 3 ─ %4 = %new(SafeRef{String}, \"bar\")::SafeRef{String}                    │╻╷ SafeRef\n7 ✓′ 4 ┄ %5 = φ (#2 => %2, #3 => %4)::SafeRef{String}                          │\n  ✓′ │   %6 = φ (#2 => %2, #3 => %4)::SafeRef{String}                          │\n  ◌  │        Base.setfield!(%5, :x, _3)::String                               │╻  setindex!\n8 ↑  │   %8 = Base.getfield(%6, :x)::String                                    │╻╷ getindex\n9 ◌  └──      return %8                                                        │","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"ϕ1 = %5 and ϕ2 = %6 are aliased and thus ReturnEscape imposed on %8 = Base.getfield(%6, :x)::String (corresponding to y = ϕ1[]) needs to be propagated to Base.setfield!(%5, :x, _3)::String (corresponding to ϕ2[] = x). In order for such escape information to be propagated correctly, the analysis should recognize that the predecessors of ϕ1 and ϕ2 can be aliased as well and equalize their escape information.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"One interesting property of such aliasing information is that it is not known at \"usage\" site but can only be derived at \"definition\" site (as aliasing is conceptually equivalent to assignment), and thus it doesn't naturally fit in a backward analysis. In order to efficiently propagate escape information between related values, EscapeAnalysis.jl uses an approach inspired by the escape analysis algorithm explained in an old JVM paper[JVM05]. That is, in addition to managing escape lattice elements, the analysis also maintains an \"equi\"-alias set, a disjoint set of aliased arguments and SSA statements. The alias set manages values that can be aliased to each other and allows escape information imposed on any of such aliased values to be equalized between them.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"Lastly, this scheme of alias/field analysis can also be generalized to analyze array operations. EscapeAnalysis currently reasons about escapes imposed on array elements using an imprecise version of the field analysis described above, where AliasEscapes doesn't try to track precise array index but rather simply records all possible values that can be aliased any elements of the array.","category":"page"},{"location":"#EA-Exception-Handling","page":"EscapeAnalysis","title":"Exception Handling","text":"","category":"section"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"It would be also worth noting how EscapeAnalysis handles possible escapes via exceptions. Naively it seems enough to propagate escape information imposed on :the_exception object to all values that may be thrown in a corresponding try block. But there are actually several other ways to access to the exception object in Julia, such as Base.current_exceptions and manual catch of rethrown object. For example, escape analysis needs to account for potential escape of r in the example below:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> const Gx = Ref{Any}();\n\njulia> @noinline function rethrow_escape!()\n           try\n               rethrow()\n           catch err\n               Gx[] = err\n           end\n       end;\n\njulia> get′(x) = isassigned(x) ? x[] : throw(x);\n\njulia> code_escapes() do\n           r = Ref{String}()\n           local t\n           try\n               t = get′(r)\n           catch err\n               t = typeof(err)   # `err` (which `r` aliases to) doesn't escape here\n               rethrow_escape!() # but `r` escapes here\n           end\n           return t\n       end\n#9() in Main at REPL[12]:2\n2  X  1 ── %1  = %new(Base.RefValue{String})::Base.RefValue{String}            │╻╷ Ref\n4  ◌  2 ── %2  = $(Expr(:enter, #8))                                           │\n5  ◌  3 ── %3  = Base.isdefined(%1, :x)::Bool                                  │╻╷ get′\n   ◌  └───       goto #5 if not %3                                             ││\n   ↑  4 ── %5  = Base.getfield(%1, :x)::String                                 ││╻  getindex\n   ◌  └───       goto #6                                                       ││\n   ◌  5 ──       Main.throw(%1)::Union{}                                       ││\n   ◌  └───       unreachable                                                   ││\n   ◌  6 ──       $(Expr(:leave, 1))                                            │\n   ◌  7 ──       goto #10                                                      │\n   ◌  8 ──       $(Expr(:leave, 1))                                            │\n   ◌  9 ── %12 = $(Expr(:the_exception))::Any                                  │\n7  ↑  │    %13 = Main.typeof(%12)::DataType                                    │\n8  ◌  │          invoke Main.rethrow_escape!()::Any                            │\n   ◌  └───       $(Expr(:pop_exception, :(%2)))::Any                           │\n10 ↑  10 ┄ %16 = φ (#7 => %5, #9 => %13)::Union{DataType, String}              │\n   ◌  └───       return %16                                                    │","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"It requires a global analysis in order to correctly reason about all possible escapes via existing exception interfaces. For now we always propagate the topmost escape information to all potentially thrown objects conservatively, since such an additional analysis might not be worthwhile to do given that exception handling and error path usually don't need to be very performance sensitive, and also optimizations of error paths might be very ineffective anyway since they are often even \"unoptimized\" intentionally for latency reasons.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"x::EscapeLattice's x.ThrownEscape property records SSA statements where x can be thrown as an exception. Using this information EscapeAnalysis can propagate possible escapes via exceptions limitedly to only those may be thrown in each try region:","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"julia> result = code_escapes((String,String)) do s1, s2\n           r1 = Ref(s1)\n           r2 = Ref(s2)\n           local ret\n           try\n               s1 = get′(r1)\n               ret = sizeof(s1)\n           catch err\n               global g = err # will definitely escape `r1`\n           end\n           s2 = get′(r2)      # still `r2` doesn't escape fully\n           return s2\n       end\n#11(X _2::String, ↑ _3::String) in Main at REPL[13]:2\n2  X  1 ── %1  = %new(Base.RefValue{String}, _2)::Base.RefValue{String}   │╻╷╷ Ref\n3  *′ └─── %2  = %new(Base.RefValue{String}, _3)::Base.RefValue{String}   │╻╷╷ Ref\n5  ◌  2 ── %3  = $(Expr(:enter, #8))                                      │\n   *′ └─── %4  = ϒ (%2)::Base.RefValue{String}                            │\n6  ◌  3 ── %5  = Base.isdefined(%1, :x)::Bool                             │╻╷  get′\n   ◌  └───       goto #5 if not %5                                        ││\n   X  4 ──       Base.getfield(%1, :x)::String                            ││╻   getindex\n   ◌  └───       goto #6                                                  ││\n   ◌  5 ──       Main.throw(%1)::Union{}                                  ││\n   ◌  └───       unreachable                                              ││\n7  ◌  6 ──       nothing::typeof(Core.sizeof)                             │╻   sizeof\n   ◌  │          nothing::Int64                                           ││\n   ◌  └───       $(Expr(:leave, 1))                                       │\n   ◌  7 ──       goto #10                                                 │\n   *′ 8 ── %15 = φᶜ (%4)::Base.RefValue{String}                           │\n   ◌  └───       $(Expr(:leave, 1))                                       │\n   X  9 ── %17 = $(Expr(:the_exception))::Any                             │\n9  ◌  │          (Main.g = %17)::Any                                      │\n   ◌  └───       $(Expr(:pop_exception, :(%3)))::Any                      │\n11 *′ 10 ┄ %20 = φ (#7 => %2, #9 => %15)::Base.RefValue{String}           │\n   ◌  │    %21 = Base.isdefined(%20, :x)::Bool                            ││╻   isassigned\n   ◌  └───       goto #12 if not %21                                      ││\n   ↑  11 ─ %23 = Base.getfield(%20, :x)::String                           │││╻   getproperty\n   ◌  └───       goto #13                                                 ││\n   ◌  12 ─       Main.throw(%20)::Union{}                                 ││\n   ◌  └───       unreachable                                              ││\n12 ◌  13 ─       return %23                                               │","category":"page"},{"location":"#Analysis-Usage","page":"EscapeAnalysis","title":"Analysis Usage","text":"","category":"section"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"When using EscapeAnalysis in Julia's high-level compilation pipeline, we can run analyze_escapes(ir::IRCode) -> estate::EscapeState to analyze escape information of each SSA-IR element in ir.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"Note that it should be most effective if analyze_escapes runs after inlining, as EscapeAnalysis's interprocedural escape information handling is limited at this moment.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"Since the computational cost of analyze_escapes is not that cheap, it is more ideal if it runs once and succeeding optimization passes incrementally update     the escape information upon IR transformation.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"EscapeAnalysis.analyze_escapes\nEscapeAnalysis.EscapeState\nEscapeAnalysis.cache_escapes!","category":"page"},{"location":"#EscapeAnalysis.analyze_escapes","page":"EscapeAnalysis","title":"EscapeAnalysis.analyze_escapes","text":"analyze_escapes(ir::IRCode, nargs::Int) -> estate::EscapeState\n\nAnalyzes escape information in ir. nargs is the number of actual arguments of the analyzed call.\n\n\n\n\n\n","category":"function"},{"location":"#EscapeAnalysis.EscapeState","page":"EscapeAnalysis","title":"EscapeAnalysis.EscapeState","text":"estate::EscapeState\n\nExtended lattice that maps arguments and SSA values to escape information represented as EscapeLattice. Escape information imposed on SSA IR element x can be retrieved by estate[x].\n\n\n\n\n\n","category":"type"},{"location":"#EscapeAnalysis.cache_escapes!","page":"EscapeAnalysis","title":"EscapeAnalysis.cache_escapes!","text":"cache_escapes!(linfo::MethodInstance, estate::EscapeState, _::IRCode)\n\nTransforms escape information of estate for interprocedural propagation, and caches it in a global cache that can then be looked up later when linfo callsite is seen again.\n\n\n\n\n\n","category":"function"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"[LatticeDesign]: Our type inference implementation takes the alternative approach, where each lattice property is represented by a special lattice element type object. It turns out that it started to complicate implementations of the lattice operations mainly because it often requires conversion rules between each lattice element type object. And we are working on overhauling our type inference lattice implementation with EscapeLattice-like lattice design.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"[MM02]: A Graph-Free approach to Data-Flow Analysis.      Markas Mohnen, 2002, April.      https://api.semanticscholar.org/CorpusID:28519618.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"[BackandForth]: Our type inference algorithm in contrast is implemented as a forward analysis, because type information usually flows from \"definition\" to \"usage\" and it is more natural and effective to propagate such information in a forward way.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"[Dynamism]: In some cases, however, object fields can't be analyzed precisely. For example, object may escape to somewhere EscapeAnalysis can't account for possible memory effects on it, or fields of the objects simply can't be known because of the lack of type information. In such cases AliasEscapes property is raised to the topmost element within its own lattice order, and it causes succeeding field analysis to be conservative and escape information imposed on fields of an unanalyzable object to be propagated to the object itself.","category":"page"},{"location":"","page":"EscapeAnalysis","title":"EscapeAnalysis","text":"[JVM05]: Escape Analysis in the Context of Dynamic Compilation and Deoptimization.       Thomas Kotzmann and Hanspeter Mössenböck, 2005, June.       https://dl.acm.org/doi/10.1145/1064979.1064996.","category":"page"}]
}
