# [Style Guide](@id style_guide)

The formatting, naming, and organizational conventions used in
`DisjunctiveProgramming`. We ask contributors to follow them so the source stays
consistent.

## File Organization

Source files live in `./src/`, tests in `./test/`, documentation in `./docs/`,
and package extensions in `./ext/`.

`src/DisjunctiveProgramming.jl` is the module file. It holds imports, includes,
and the export loop, and should not define functions or types directly. New
types belong in `src/datatypes.jl`. Each reformulation method gets its own file
named after it, as `src/bigm.jl` and `src/hull.jl` do.

Test files mirror the source layout under `test/`, with one file per topic, and
each is included from `test/runtests.jl`.

## Julia Code

The base is the [JuMP style guide](https://jump.dev/JuMP.jl/stable/developers/style/).
The following are the additions specific to this package.

**Keep lines to 80 characters.** Apply this to new and modified code only. Do
not reformat existing lines you are not otherwise changing.

Use the full width before wrapping. A line under 80 characters stays on one
line, and a wrapped line should fill close to 80 before continuing:

```julia
# Avoid, wraps at 39 characters for no reason
sep = build_subproblem(
    model, dec_vars, Hull(), method)

# Prefer, fits on one line
sep = build_subproblem(model, dec_vars, Hull(), method)
```

**Write function signatures one of two ways.** Either the whole signature on one
line, or every parameter on its own line with the closing parenthesis at the
argument indent level. Never split partway, leaving some arguments beside the
function name and the rest below:

```julia
# One line
function _get_M_value(func, set, method)

# Or one parameter per line
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::JuMP.AbstractVariableRef,
    method::BigM
    ) where {T, S <: _MOI.LessThan}
```

**Separate sections with a banner comment**, as the existing source does:

```julia
################################################################################
#                              SECTION NAME
################################################################################
```

**Prefix internal functions and types with an underscore.** These are excluded
from the export loop in the module file, so the underscore is what makes a name
private.

## Naming

Name an object for its mathematical role in the formulation, spelled out in
full. A reader should be able to map an identifier to the formulation without
opening the referenced paper.

- A name says what the object **is** in the formulation, not where it sits in
  the algorithm. Prefer `affine_part` and `quad_matrix` over `rest`, `tmp`, or
  `result`.
- A bare adjective is not a name. Pair it with the noun it qualifies, so `pure`
  becomes `quad_part` and `rest` becomes `affine_part`.
- Avoid single-letter identifiers, even for symbols taken from a paper. Write
  `quad_matrix` rather than `Q`, and `epigraph_vref` rather than `t`. Math
  symbols belong in comments and docstrings.
- Do not invent abbreviation suffixes. When a value keeps its role through a
  transformation, rebind the same name rather than coining a stage variant.
- Reuse the established suffixes with descriptive stems: `*_vref` for variable
  references, `*_func` for constraint functions, `*_part` for split components,
  and `*_con` for constraints.
- Prefer the domain term from the referenced formulation over an invented one.
- Name a helper for what the caller receives, not for the mechanism inside it.

## Docstrings and Comments

Every public function, macro, and type needs a docstring. The signature comes
first, indented, followed by a description:

```julia
"""
    function_name(
        arg1::Type1,
        arg2::Type2;
        [kwarg::Type = default]
        )::ReturnType

Description of what the function does.

## Keyword Arguments
- `kwarg::Type`: Description.

## Returns
- `ReturnType`: Description.
"""
```

A type docstring lists its fields instead:

```julia
"""
    BigM{T} <: AbstractReformulationMethod

A type for using the big-M reformulation approach for disjunctive constraints.

**Fields**
- `value::T`: Big-M value (default = `1e9`).
- `tight::Bool`: Attempt to tighten the Big-M value (default = `true`)?
"""
```

Internal functions take a brief comment above them rather than a docstring.

Keep comments terse. The existing reformulation files run around one comment
line per ten lines of code, and that is the target. Do not cite papers or
equation numbers in comments. That context belongs in the docstring or in the
documentation.

## Unit Tests

Write one `test_*` function per case, then collect them in `@testset` blocks at
the bottom of the file:

```julia
function test_feature_case()
    model = GDPModel()
    @variable(model, x)
    @test condition
end

@testset "Feature Name" begin
    test_feature_case()
    test_feature_other_case()
end
```

Cover the constraint types systematically. A reformulation touches `MOI.LessThan`,
`MOI.GreaterThan`, `MOI.EqualTo`, and `MOI.Interval` for scalar constraints, and
`MOI.Nonpositives`, `MOI.Nonnegatives`, and `MOI.Zeros` for vector constraints.
A method is not tested until all of them are.

Add the new test file to `test/runtests.jl`. The suite also runs
[Aqua.jl](https://github.com/JuliaTesting/Aqua.jl) quality checks, so a new
dependency or an ambiguous method signature will surface there.

## Documentation Pages

Keep documentation content concise, and prefer examples and lists over long
prose. Avoid the passive voice.

The documentation has two parallel trees. A page under `docs/src/guide/`
teaches, and its counterpart under `docs/src/manual/` holds the docstrings.
Both use the same page names. A new docstring must be added to the appropriate
`@docs` block on the manual page, since the manual pages list entries explicitly
rather than collecting them automatically.

Guide examples use `jldoctest` blocks with a page-scoped label, so state carries
across blocks on a page and Documenter checks the printed output against what is
written.

Build the documentation locally before opening a pull request:

```
julia --project=docs docs/make.jl
```

The build runs every example and fails on an unresolved cross-reference, a
docstring missing from its manual page, or an example that no longer runs.

Do not transcribe example output by hand. Write the block with its output blank,
add `doctest = :fix` to the `makedocs` call in `docs/make.jl`, and run the build
once. Documenter executes each block and writes the real output back into the
source file. Then remove `doctest = :fix` and build again to verify.

That is also the fix when a JuMP or Julia upgrade changes how a model prints and
the doctests start failing. The stored output is stale rather than wrong, and
regenerating it is a single run.
