[![CI](https://github.com/aviatesk/EscapeAnalysis.jl/actions/workflows/ci.yml/badge.svg)](https://github.com/aviatesk/EscapeAnalysis.jl/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/aviatesk/EscapeAnalysis.jl/branch/master/graph/badge.svg?token=ADEKPZRUJH)](https://codecov.io/gh/aviatesk/EscapeAnalysis.jl)

`EscapeAnalysis` is a simple module that collects escape information from Julia's optimization IR (i.e. `IRCode`).

This analysis works on a lattice called `x::EscapeLattice`, which holds the following properties:
- `x.Analyzed::Bool`: not formally part of the lattice, indicates `x` has not been analyzed at all
- `x.ReturnEscape::Bool`: indicates `x` may escape to the caller via return
- `x.ThrownEscape::Bool`: indicates `x` may escape to somewhere through an exception
- `x.EscapeSites::BitSet`: records program counters (SSA numbers) where `x` can escape
  (via any kinds of escape)
- `x.FieldSets::Union{Vector{IdSet{Any}},Bool}`: maintains all possible values that impose
  escape information on fields of `x`
- `x.ArgEscape::Int` (not implemented yet): indicates it will escape to the caller through
  `setfield!` on argument(s)

These attributes can be combined to create a partial lattice that has a finite height, given
that input program has a finite number of statements, which is assured by Julia's semantics.

Escape analysis implementation is based on the data-flow algorithm described in the paper[^MM02].
The analysis works on the lattice of `EscapeLattice` and transitions lattice elements from the
bottom to the top until every lattice gets converged to a fixed point by maintaining a (conceptual)
working set that contains program counters corresponding to  remaining SSA statements to be analyzed.
The analysis only manages a single global state that tracks `EscapeLattice` of each argument
and SSA statement, but also note that some flow-sensitivity is being encoded as program
counters recorded in the `EscapeSites` property of each lattice element, which can be
combined with domination analysis to reason about flow-sensitivity if necessary.

One distinctive design of this analysis is that escape information is propagated in a
_backward_ way, i.e. data flows _from usages to definitions_.
For example, in the code snippet below, EA first analyzes the statement `return obj` and
imposes `ReturnEscape` on `obj`, and then it analyzes `obj = Expr(:new, Obj, val)` and
propagates `ReturnEscape` imposed on `obj` to `val`:
```julia
obj = Expr(:new, Obj, val) # lowered from `Obj(val)`
return obj
```
The key observation here is that this backward analysis allows escape information to flow
naturally along the use-def chain rather than control-flow, which can better handled by
forward analysis otherwise. As a result, this scheme enables a very simple implementation of
escape analysis, e.g. `PhiNode` for example can be handled relatively easily by propagating
escape information imposed on it to its predecessors.

It would be also worth noting the `FieldSets` property enables a backward field analysis.
It tracks all possibilities that _can escape fields of object_, which can be analyzed at
"usage" sites, and escape information imposed on those tracked possibilities are propagated
to the actual field values later at "definition" site. Especially, the analysis records a
value that may impose escape information on field of object at `getfield` call, and then it
propagates that escape information to the field when analyzing `Expr(:new)` or `setfield!`
expressions.
```julia
obj = Expr(:new, Obj, val)
v = getfield(obj, :val)
return v
```
In the example above, `ReturnEscape` imposed on `v` is _not_ directly propagated to `obj`.
Rather the identity of `v` is recorded in `obj`'s `FieldSets[1]` and then `v`'s escape
information is propagated to `val` when `obj = Expr(:new, Obj, val)` is analyzed.

Finally, the analysis also needs to track which values can be aliased to each other. This is
needed because in Julia IR, the same object is sometimes represented by different IR elements.
Since the analysis maintains `EscapeLattice` per IR element, we need to make sure those different
IR elements that actually represent the same object to share the same escape information.
Those program constructs that return the same object as their operand(s) like `PiNode` and
`typeassert` are obvious examples that require this escape information aliasing.
But the escape information equalization between aliased values is needed for other cases as
well, most notably, it is necessary for correctly reasoning about mutations on `PhiNode`.
Now let's consider the following example; `ϕ1` and `ϕ2` are aliased and thus `ReturnEscape`
imposed on `y = ϕ1[]` needs to be propagated to `ϕ2[] = x`. The escape information can be
propagated if the escape states of _predecessors_ of `ϕ1` and `ϕ2` (i.e. those two
`RefValue` objects) are shared ("equalized"):
```julia
if cond::Bool
    ϕ2 = ϕ1 = Ref("foo")
else
    ϕ2 = ϕ1 = Ref("bar")
end
ϕ2[] = x::String
y = ϕ1[]
return y
```

However, one interesting property of such alias information is that it is not known at "usage"
site but can be derived at "definition" site (as aliasing is conceptually equivalent to assignment),
and thus it doesn't naturally flow in a backward way. In order to efficiently propagate escape
information between related values, EscapeAnalysis.jl uses an approach inspired by the escape
analysis algorithm explained in this old JVM paper[^JVM05]. That is, in addition to managing
escape lattice elements, the analysis also maintains an "equi"-alias set, a disjoint set of
aliased arguments and SSA statements. The alias set records values that can be aliased to
each other and allows new escape information imposed on any of such aliased values to be
equalized between them.

[^MM02]: _A Graph-Free approach to Data-Flow Analysis_.
         Markas Mohnen, 2002, April.
         <https://api.semanticscholar.org/CorpusID:28519618>.

[^JVM05]: _Escape Analysis in the Context of Dynamic Compilation and Deoptimization_.
          Thomas Kotzmann and Hanspeter Mössenböck, 2005, June.
          <https://dl.acm.org/doi/10.1145/1064979.1064996>.
