A simple module that collects escape information from Julia optimization IR (i.e. `IRCode`).

Couple of notes about this escape analysis:
- the analysis is based on the [data-flow analysis](https://aviatesk.github.io/posts/data-flow-problem/) approach
- it is a backward-analysis, i.e. escape information will flow from usage site to definition site
- the algorithm works by updating the working set that contains program counters corresponding to SSA statements until every statement gets converged to a fixed point
- it is flow-insenstive, i.e. doesn't distinguish escape information on the same "object" but at different locations

This escape analysis works on a lattice called `EscapeLattice,`, which holds the following properties:
- `x.Analyzed::Bool`: not formally part of the lattice, indicates this statement has not been analyzed at all
- `x.ReturnEscape::Bool`: indicates it will escape to the caller via return (possibly as a field)
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
- [ ] make it flow-sensitive and implement a `finalizer` elision optimization (#17)
- [ ] port to the Julia base, and implement heap-to-stack optimization pass
- [ ] circumvent too conservative escape through potential `throw` calls by copying stack-to-heap on exception (#15)
