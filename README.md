[![CI](https://github.com/aviatesk/EscapeAnalysis.jl/actions/workflows/ci.yml/badge.svg)](https://github.com/aviatesk/EscapeAnalysis.jl/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/aviatesk/EscapeAnalysis.jl/branch/master/graph/badge.svg?token=ADEKPZRUJH)](https://codecov.io/gh/aviatesk/EscapeAnalysis.jl)

A simple module that collects escape information from Julia optimization IR (i.e. `IRCode`).

Couple of notes about this escape analysis:
- the analysis is based on the [data-flow analysis](https://aviatesk.github.io/posts/data-flow-problem/) approach
- it is a backward-analysis, i.e. escape information will flow from usage site to definition site
- the algorithm works by updating the working set that contains program counters corresponding to SSA statements until every statement gets converged to a fixed point
- it only manages a single global state, some flow-sensitivity is encoded as `EscapeLattice` properties

This escape analysis works on a lattice called `EscapeLattice`, which holds the following properties:
- `x.Analyzed::Bool`: not formally part of the lattice, indicates this statement has not been analyzed at all
- `x.ReturnEscape::BitSet`: keeps SSA numbers of return statements where it can be returned to the caller
  * `isempty(x.ReturnEscape)` means it never escapes to the caller
  * otherwise it indicates it will escape to the caller via return (possibly as a field),
    where `0 ∈ x.ReturnEscape` has the special meaning that it's visible to the caller
    simply because it's passed as call argument
- `x.ThrownEscape::Bool`: indicates it may escape to somewhere through an exception (possibly as a field)
- `x.GlobalEscape::Bool`: indicates it may escape to a global space an exception (possibly as a field)
- `x.ArgEscape::Int` (not implemented yet): indicates it will escape to the caller through `setfield!` on argument(s)
  * `-1` : no escape
  * `0` : unknown or multiple
  * `n` : through argument N

These attributes can be combined to create a partial lattice that has a finite height:
- `AllEscape`: the topmost element of this lattice, meaning it will escape to everywhere
- `ReturnEscape`, `Escape`: intermediate lattice elements
- `NoEscape`: the bottom element of this lattice

The escape analysis will transition these elements from the bottom to the top,
in the same way as Julia's native type inference routine.
An abstract state will be initialized with the bottom(-like) elements:
- the call arguments are initialized as `ReturnEscape`, because they're visible from a caller immediately
- the other states are initialized as `NotAnalyzed`, which is a special lattice element that
  is slightly lower than `NoEscape`, but at the same time doesn't represent any meaning
  other than it's not analyzed yet (thus it's not formally part of the lattice).

TODO:
- [ ] implement more builtin function handlings, and make escape information more accurate
- [ ] make analysis take into account alias information
- [ ] implement `finalizer` elision optimization ([#17](https://github.com/aviatesk/EscapeAnalysis.jl/issues/17))
- [ ] circumvent too conservative escapes through potential `throw` calls by copying stack-to-heap on exception ([#15](https://github.com/aviatesk/EscapeAnalysis.jl/issues/15))
