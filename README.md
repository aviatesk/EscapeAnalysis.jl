A simple module that collects escape information from Julia optimization IR (i.e. `IRCode`).

Couple of notes about this escape analysis:
- the analysis is based on the [data-flow analysis](https://aviatesk.github.io/posts/data-flow-problem/) approach
- it is a backward-analysis, i.e. escape information will flow from usage site to definition site
- the algorithm works by updating the working set that contains program counters corresponding to SSA statements until every statement gets converged to a fixed point
- it is flow-insenstive, i.e. doesn't distinguish escape information on the same "object" but at different locations

The analysis will work on a lattice that has a finite height, and can express the following "escape properties":
- `NoInformation`: the top element of this lattice, meaning no information is derived
- `NoEscape`: the second topmost element of this lattice, meaning it will not escape from this local frame
- `ReturnEscape`: a lattice that is lower than `NoEscape`, meaning it will escape to the caller
- `Escape`: the bottom element of this lattice, meaning it will escape to somewhere

TODO:
- [ ] implement more builtin function handlings, and make escape information more accurate (it's sound, but too conservative currently)
  * [ ] (related to above) do more smart analysis on aliased pointers to some extent
- [ ] maybe make it flow-sensitive (with sparse analysis state)
- [ ] port to the Julia base, and implement optimization passes that use this information
