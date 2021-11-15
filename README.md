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

Escape analysis implementation is based on the data-flow algorithm described in the paper [^MM02].
The analysis works on the lattice of [`EscapeLattice`](@ref) and transitions lattice elements
from the bottom to the top in a _backward_ way, i.e. data flows from usage cites to definitions,
until every lattice gets converged to a fixed point by maintaining a (conceptual) working set
that contains program counters corresponding to remaining SSA statements to be analyzed.
The analysis only manages a single global state that tracks `EscapeLattice` of each argument
and SSA statement, but also note that some flow-sensitivity is encoded as program counters
recorded in the `EscapeSites` property of each each lattice element.

[^MM02]: _A Graph-Free approach to Data-Flow Analysis_.
         Markas Mohnen, 2002, April.
         <https://api.semanticscholar.org/CorpusID:28519618>.
