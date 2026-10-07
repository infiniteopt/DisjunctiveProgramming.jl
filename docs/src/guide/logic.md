```@meta
DocTestFilters = [r"≤|<=", r"≥|>=", r" == | = ", r" ∈ | in ",
                  r"MathOptInterface|MOI"]
```

# [Logical Constraints](@id logic_guide)

A guide for propositional and cardinality constraints over logical variables.
See the respective [technical manual](@ref logic_manual) for more details.

## Overview

Disjunctions express which constraints apply. Logical constraints express which
*combinations of decisions* we permit, independently of any algebraic
constraint. They come in two forms.

A *proposition* is a Boolean expression we assert to be true, such as requiring
that selecting one process implies selecting a quality check. A *cardinality
constraint* requires that a given number of logical variables from a collection
be true, such as selecting exactly two suppliers out of five.

Both forms are reformulated into linear constraints on the binary variables that
replace the logical variables. Propositions are first converted to conjunctive
normal form, which yields one linear inequality per clause.

## Logical Operators

We have five operators available. Each has a Unicode form, a written alias, and
in most cases an ASCII operator that behaves identically inside a logical
expression.

| Operation | Unicode | Alias | ASCII |
|---|---|---|---|
| Conjunction | `∧` | `logical_and` | `&&` |
| Disjunction | `∨` | `logical_or` | `\|\|` |
| Negation | `¬` | `logical_not` | `!` |
| Implication | `⟹` | `implies` | |
| Equivalence | `⇔` | `iff` | |

We enter the Unicode symbols in the Julia REPL and in most editors by typing the
LaTeX name followed by tab: `\wedge` for `∧`, `\vee` for `∨`, `\neg` for `¬`,
`\Longrightarrow` for `⟹`, and `\Leftrightarrow` for `⇔`.

## Basic Usage

We write a proposition as a Boolean expression followed by `:= true` inside
`@constraint`. Let's set up a few decisions and relate them:

```jldoctest gdp_logic; setup = :(using DisjunctiveProgramming)
julia> model = GDPModel();

julia> @variable(model, process_a, Logical);

julia> @variable(model, process_b, Logical);

julia> @variable(model, quality_check, Logical);

julia> @variable(model, premium_grade, Logical);

julia> @constraint(model, (process_a ∨ process_b) ⟹ quality_check := true);

julia> @constraint(model, premium_grade ⟹ (process_a ∧ quality_check) := true);

julia> @constraint(model, ¬(process_a ∧ process_b) := true);
```

The written aliases and ASCII operators give us the same constraints, which is
useful when we want a source file to stay in plain ASCII:

```jldoctest gdp_logic
julia> @constraint(model, logical_or(process_a, process_b) := true);

julia> @constraint(model, (process_a && quality_check) := true);
```

!!! warning
    A proposition must relate more than one variable. Asserting a single
    variable, as in `@constraint(model, process_a := true)` or
    `@constraint(model, ¬process_a := true)`, is an error. Use
    `fix(process_a, true)` or `fix(process_a, false)` instead, which expresses
    the same thing without adding a constraint to the reformulated program.

### Cardinality Constraints

[`Exactly`](@ref), [`AtLeast`](@ref), and [`AtMost`](@ref) constrain how many
variables in a collection are true. We use them as JuMP sets, with the
collection on the left of `in`:

```jldoctest gdp_logic
julia> selection = GDPModel();

julia> @variable(selection, suppliers[1:5], Logical);

julia> @constraint(selection, suppliers in Exactly(2));

julia> @constraint(selection, suppliers in AtLeast(1));

julia> @constraint(selection, suppliers in AtMost(3));
```

The count may itself be a logical variable rather than an integer, which makes
the requirement conditional on another decision:

```jldoctest gdp_logic
julia> @variable(selection, expand, Logical);

julia> @constraint(selection, suppliers in AtLeast(expand));
```

Here we require at least one supplier when `expand` is true, and impose no
requirement when it is false.

!!! note
    Every disjunction added with [`@disjunction`](@ref) already carries an
    exclusivity requirement equivalent to `Exactly(1)` over its disjuncts, added
    automatically. We do not need to write one ourselves, and we can turn the
    behaviour off with the `exactly1` keyword when a disjunction should permit
    more than one disjunct to be selected.

## Building Larger Expressions

Operators nest, so we can describe a structured requirement in one constraint:

```jldoctest gdp_logic
julia> nested = GDPModel();

julia> @variable(nested, X[1:4], Logical);

julia> @constraint(nested, ((X[1] ∨ X[2]) ∧ (X[3] ∨ X[4])) ⟹ (X[1] ⇔ X[3]) := true);
```

Because the reformulation converts each proposition to conjunctive normal form,
a deeply nested expression can expand into a considerable number of linear
constraints. Where we can state a requirement either as one large proposition or
as several small ones, the several small ones usually give a tighter and smaller
program.

Splatting works for requirements over a whole container:

```jldoctest gdp_logic
julia> @constraint(nested, logical_or(X...) := true);
```
