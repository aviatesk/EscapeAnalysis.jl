[![CI](https://github.com/aviatesk/EscapeAnalysis.jl/actions/workflows/ci.yml/badge.svg)](https://github.com/aviatesk/EscapeAnalysis.jl/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/aviatesk/EscapeAnalysis.jl/branch/master/graph/badge.svg?token=ADEKPZRUJH)](https://codecov.io/gh/aviatesk/EscapeAnalysis.jl)

`EscapeAnalysis` is a simple module that collects escape information from Julia's optimization IR (i.e. `IRCode`).

This analysis works on a lattice called `x::EscapeLattice`, which holds the following properties:
- `x.Analyzed::Bool`: not formally part of the lattice, indicates `x` has not been analyzed at all
- `x.ReturnEscape::Bool`: indicates `x` may escape to the caller via return (possibly as a field),
    where `x.ReturnEscape && 0 ∈ x.EscapeSites` has the special meaning that it's visible to
    the caller simply because it's passed as call argument
- `x.ThrownEscape::Bool`: indicates `x` may escape to somewhere through an exception (possibly as a field)
- `x.EscapeSites::BitSet`: records program counters (SSA numbers) where `x` can escape
- `x.FieldSets::Union{Vector{IdSet{Any}},Bool}`: maintains the sets of possible values of fields of `x`:
  * `x.FieldSets === false` indicates the fields of `x` isn't analyzed yet
  * `x.FieldSets === true` indicates the fields of `x` can't be analyzed, e.g. the type of `x`
    is not concrete and thus the number of its fields can't known precisely
  * otherwise `x.FieldSets::Vector{IdSet{Any}}` holds all the possible values of each field,
    where `x.FieldSets[i]` keeps all possibilities that the `i`th field can be
- `x.ArgEscape::Int` (not implemented yet): indicates it will escape to the caller through `setfield!` on argument(s)
  * `-1` : no escape
  * `0` : unknown or multiple
  * `n` : through argument N

These attributes can be combined to create a partial lattice that has a finite height, given
that input program has a finite number of statements, which is assured by Julia's semantics.

There are utility constructors to create common `EscapeLattice`s, e.g.,
- `NoEscape()`: the bottom element of this lattice, meaning it won't escape to anywhere
- `AllEscape()`: the topmost element of this lattice, meaning it will escape to everywhere

The escape analysis will transition these elements from the bottom to the top,
in the same direction as Julia's native type inference routine.
An abstract state will be initialized with the bottom(-like) elements:
- the call arguments are initialized as `ArgumentReturnEscape()`, because they're visible from a caller immediately
- the other states are initialized as `NotAnalyzed()`, which is a special lattice element that
  is slightly lower than `NoEscape`, but at the same time doesn't represent any meaning
  other than it's not analyzed yet (thus it's not formally part of the lattice).

Escape analysis implementation is based on the data-flow algorithm described in the old paper [^MM02].
The analysis works on the lattice of [`EscapeLattice`](@ref) and transitions lattice elements
from the bottom to the top in a _backward_ way, i.e. data flows from usage cites to definitions,
until every lattice gets converged to a fixed point by maintaining a (conceptual) working set
that contains program counters corresponding to remaining SSA statements to be analyzed.
The analysis only manages a single global state that tracks `EscapeLattice` of each argument
and SSA statement, but also note that some flow-sensitivity is encoded as program counters
recorded in the `EscapeSites` property of each each lattice element.

The analysis also collects alias information using an approach, which is inspired by
the escape analysis algorithm explained in yet another old paper [^JVM05].
In addition to managing escape lattice elements, the analysis state also maintains an "alias set",
which is implemented as a disjoint set of aliased arguments and SSA statements.
When the fields of object `x` are known precisely (i.e. `x.FieldSets isa Vector{IdSet{Any}}` holds),
the alias set is updated each time `z = getfield(x, y)` is encountered in a way that `z` is
aliased to all values of `x.FieldSets[y]`, so that escape information imposed on `z` will be
propagated to all the aliased values and `z` can be replaced with an aliased value later.
Note that in a case when the fields of object `x` can't known precisely (i.e. `x.FieldSets` is `true`),
when `z = getfield(x, y)` is analyzed, escape information of `z` is propagated to `x` rather
than any of `x`'s fields, which is the most conservative propagation since escape information
imposed on `x` will end up being propagated to all of its fields anyway at definitions of `x`
(i.e. `:new` expression or `setfield!` call).

[^MM02]: _A Graph-Free approach to Data-Flow Analysis_.
         Markas Mohnen, 2002, April.
         <https://api.semanticscholar.org/CorpusID:28519618>.

[^JVM05]: _Escape Analysis in the Context of Dynamic Compilation and Deoptimization_.
          Thomas Kotzmann and Hanspeter Mössenböck, 2005, June.
          <https://dl.acm.org/doi/10.1145/1064979.1064996>.
