# DisjunctiveProgramming.jl

A Generalized Disjunctive Programming (GDP) extension to JuMP.

![logo](assets/logo.png)

[![codecov](https://codecov.io/gh/infiniteopt/DisjunctiveProgramming.jl/graph/badge.svg?token=3FRPGMWF0J)](https://codecov.io/gh/infiniteopt/DisjunctiveProgramming.jl)
[![Docs](https://img.shields.io/badge/docs-stable-blue.svg)](https://infiniteopt.github.io/DisjunctiveProgramming.jl/stable/)
[![Docs](https://img.shields.io/badge/docs-latest-blue.svg)](https://infiniteopt.github.io/DisjunctiveProgramming.jl/dev/)

## What is DisjunctiveProgramming?

Generalized disjunctive programming lets us state a discrete decision as a
choice between alternative sets of constraints, rather than encoding it by hand
with binary variables and hand-tuned coefficients. We write the disjunction, and
the package turns it into a mixed-integer program for us.

`DisjunctiveProgramming` extends `JuMP` with the modeling objects this needs:

- **Logical variables**, Boolean decisions of the form ``Y \in \{\text{false}, \text{true}\}``.
- **Disjunct constraints**, ordinary algebraic constraints enforced only when
  their logical variable is true.
- **Disjunctions**, groups of mutually exclusive disjuncts, which may be nested.
- **Logical constraints**, propositions relating logical variables through
  Boolean algebra.
- **Cardinality constraints**, requiring that exactly, at least, or at most a
  given number of logical variables be true.

With `InfiniteOpt` loaded, all of these carry over to continuous domains, where
a disjunction is decided over time, space, or uncertainty rather than once for
the whole problem.

It then provides six reformulations that turn all of the above into a
mixed-integer program: Big-M, Multiple Big-M, Convex Hull, P-Split, Cutting
Planes, and solver-native Indicator constraints. A seventh method, Direct,
skips the encoding and hands each disjunction to the solver as a single
constraint in a `DisjunctionSet`, for solvers that work on disjunctions
themselves. Because the modeling layer is kept separate from the encoding, we
can switch between them on one model and compare.

## Installation

```julia
using Pkg
Pkg.add("DisjunctiveProgramming")
```

`DisjunctiveProgramming` will also need a mixed-integer solver such as
[HiGHS](https://github.com/jump-dev/HiGHS.jl) or
[Gurobi](https://github.com/jump-dev/Gurobi.jl) to solve the reformulated
models.

## First Steps

New users should start with the [Quick Start Guide](@ref quick_start), which
builds, reformulates, and solves a complete model in a few lines.

## How to Use the Documentation

The documentation is organized into four parts:

- The **Quick Start Guide** builds one complete model end to end. Start here.
- The **User Guide** explains each modeling object in turn, with runnable
  examples. Every page opens with an overview and a basic usage section, then
  covers queries and modification.
- The **API Manual** holds the docstrings, organized under the same page names
  as the User Guide. Use it to look up a signature or a keyword argument.
- **Development** is for contributors. It covers how to get started, how to add
  a reformulation method or support a new model type, and the style conventions
  the package follows.

## Reference

The theory behind the GDP modeling paradigm is described in the following references:

- [JuliaCon 2022 Proceedings](https://proceedings.juliacon.org/papers/10.21105/jcon.00117)
- [Perez and Grossmann (2023)](https://arxiv.org/abs/2303.04375)
- [Generalized Disjunctive Programming](https://optimization.cbe.cornell.edu/index.php?title=Convex_generalized_disjunctive_programming_(GDP))
- [Disjunctive Inequalities](https://optimization.cbe.cornell.edu/index.php?title=Disjunctive_inequalities)

## Citing

[![DOI](https://proceedings.juliacon.org/papers/10.21105/jcon.00117/status.svg)](https://doi.org/10.21105/jcon.00117)

If you use DisjunctiveProgramming.jl in your research, we would greatly appreciate your
citing it.

```latex
@article{Perez2023,
  title = {DisjunctiveProgramming.jl: Generalized Disjunctive Programming Models and Algorithms for JuMP},
  author = {Hector D. Perez and Shivank Joshi and Ignacio E. Grossmann},
  journal = {Proceedings of the JuliaCon Conferences},
  year = {2023},
  publisher = {The Open Journal},
  volume = {1},
  number = {1},
  pages = {117}
}
```

## Release Notes

Prior to `v0.4.0`, the package did not leverage the JuMP extension capabilities and was not as robust. For these earlier releases, refer to [Perez, Joshi, and Grossmann, 2023](https://arxiv.org/abs/2304.10492v1) and the following [JuliaCon 2022 Talk](https://www.youtube.com/watch?v=AMIrgTTfUkI).

## Contributing

`DisjunctiveProgramming` is being actively developed and suggestions or other forms of contribution are encouraged.
There are many ways to contribute to this package. Feel free to create an issue to address questions or provide feedback.
