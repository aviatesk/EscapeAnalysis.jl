A simple module that collects escape information from Julia optimization IR (i.e. `IRCode`).

Couple of notes about this escape analysis:
- the analysis is based on the [abstract interpration](https://aviatesk.github.io/posts/data-flow-problem/) framework
- it is a backward-analysis, i.e. escape information will flow from usage site to definition site
- the algorithm works by keep updating the working set that contains program counters of unconverted SSA statements until every statement gets converged
- it is flow-insenstive, i.e. doesn't distinguish escape information on the same "object" but at different locations

The analysis will work on a lattice that has finite height, and can express the following "escape properties":
- `NoInformation`: the top element of this lattice, meaning no information is derived
- `NoEscape`: the second topmost element of this lattice, meaning it will not escape from this local frame
- `ReturnEscape`: a lattice that is lower than `NoEscape`, meaning it will escape to the callee
- `Escape`: the bottom element of this lattice, meaning it will escape to somewhere

TODO:
- [ ] implement more handlings of builtin function calls, and make escape information more precise
- [ ] make it flow-sensitive ?
- [ ] port to the Julia base, and implement optimization passes that use this information
