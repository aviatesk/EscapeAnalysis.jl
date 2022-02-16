# EscapeAnalysis.jl

[![CI](https://github.com/aviatesk/EscapeAnalysis.jl/actions/workflows/ci.yml/badge.svg)](https://github.com/aviatesk/EscapeAnalysis.jl/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/aviatesk/EscapeAnalysis.jl/branch/master/graph/badge.svg?token=ADEKPZRUJH)](https://codecov.io/gh/aviatesk/EscapeAnalysis.jl)
[![](https://img.shields.io/badge/docs-dev-blue.svg)](https://aviatesk.github.io/EscapeAnalysis.jl/dev/)

`EscapeAnalysis.jl` is a staging package for the new escape analysis for Julia programming language.

This escape analysis aims to:
- leverage Julia's high-level semantics, especially reason about escapes and aliasing via
  inter-procedural calls
- be versatile enough to be used for various optimizations including
  [alias-aware SROA](https://github.com/JuliaLang/julia/pull/43888),
  [early `finalize` call insertion](https://github.com/JuliaLang/julia/pull/44056),
  [copy-free `ImmutableArray` construction](https://github.com/JuliaLang/julia/pull/42465),
  stack allocation of mutable objects,
  and so on.
- achieve a simple implementation based on a fully backward data-flow analysis implementation
  as well as a new lattice design that combines orthogonal lattice properties

Documentations on EA's design and usage are available at
[here](https://aviatesk.github.io/EscapeAnalysis.jl/dev/).

EA is currently being ported to Julia base at
[this PR](https://github.com/JuliaLang/julia/pull/43800).
Note that main development efforts are still happing here at this repository,
allowing easier experiments and quick iterations.
