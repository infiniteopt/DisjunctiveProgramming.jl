# [Getting Started](@id contribute_guide)

A guide to making your first contribution to `DisjunctiveProgramming`.

## Overview

`DisjunctiveProgramming` is actively developed, and contributions are welcome.
They do not have to be code. Reporting a confusing error message, fixing a typo
in the documentation, or adding a test for a case that is not covered are all
useful.

Please read the [Style Guide](@ref style_guide) before writing code, and open an
issue to discuss anything substantial before you start. That saves you from
building something in a direction the maintainers were not going to take.

## Reporting an Issue

Open an issue at the
[repository](https://github.com/infiniteopt/DisjunctiveProgramming.jl/issues).

A report is far easier to act on with a minimal example that reproduces the
problem, the output you got, the output you expected, and the versions involved.
`Pkg.status()` gives the last of these.

If the problem is a reformulation producing a wrong answer, include the model
and the method. Printing the reformulated model with `reformulate_model` and
`print` usually shows where the encoding went wrong, and saves a round trip.

## Step by Step

1. Fork the repository and clone your fork.
2. Create a branch for your change.
3. Develop the package in a local environment:

   ```
   julia --project -e 'using Pkg; Pkg.instantiate()'
   ```

4. Make your change, following the [Style Guide](@ref style_guide).
5. Add tests covering it. A reformulation change needs the full set of
   constraint types, not just the one that prompted the change.
6. Run the test suite:

   ```
   julia --project -e 'using Pkg; Pkg.test()'
   ```

7. Build the documentation, which runs every example in the guide:

   ```
   julia --project=docs docs/make.jl
   ```

8. Push the branch and open a pull request against `master`.

Continuous integration runs the tests and the documentation build on the pull
request, so both must pass before a merge. Running them locally first is faster
than waiting on the runner.

## Adding a Reformulation Method

This is the most common substantial contribution, and it has its own page. See
[Extensions](@ref extensions) for the hooks involved and a worked example.

A new method should cover every supported constraint type, handle logical
complements, carry a docstring listing its fields, appear in the
`## Methods` block of `docs/src/manual/methods.md`, and get a section in
[Solution Methods](@ref methods_guide) explaining when to reach for it.

## Where to Look

- `src/datatypes.jl` holds the core types, including every reformulation method.
- `src/reformulate.jl` holds the dispatch chain and the extension hooks.
- `src/bigm.jl` is the most complete reformulation to read as a reference, since
  it covers every constraint type.
- `src/indicator.jl` is the shortest, and the easiest starting point.
- `ext/InfiniteDisjunctiveProgramming.jl` shows how the package supports a model
  type it does not own.
