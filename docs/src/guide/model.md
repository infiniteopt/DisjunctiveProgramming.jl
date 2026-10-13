```@meta
DocTestFilters = [r"≤|<=", r"≥|>=", r" == | = ", r" ∈ | in ",
                  r"MathOptInterface|MOI"]
```

# [GDP Models](@id model_guide)

A guide for creating and working with generalized disjunctive
programming models. See the respective [technical manual](@ref model_manual)
for more details.

## Overview

Generalized disjunctive programming (GDP) lets us express a discrete decision as
a choice between alternative sets of constraints, rather than as an algebraic
relationship between binary variables. Each alternative is a *disjunct*, a group
of mutually exclusive disjuncts is a *disjunction*, and a Boolean *logical
variable* records which disjunct is selected. Modeling this way keeps our
formulation close to the way we would describe the problem in words, and it
defers the choice of algebraic encoding until we solve.

A [`GDPModel`](@ref) is a JuMP model that carries the extra bookkeeping we need
for this. It holds ordinary JuMP variables and constraints exactly as a `Model`
does, and adds storage for logical variables, disjunct constraints, disjunctions,
and logical constraints. None of that structure goes to a solver directly.
Instead, `optimize!` first *reformulates* the model into an equivalent
mixed-integer program using a method we choose, and then solves it. We cover the
methods in [Solution Methods](@ref methods_guide).

## Basic Usage

Let's create a GDP model with [`GDPModel`](@ref), which accepts the same
arguments as JuMP's `Model`:

```jldoctest gdp_model; setup = :(using DisjunctiveProgramming, HiGHS)
julia> model = GDPModel(HiGHS.Optimizer);

julia> set_silent(model)
```

Now we add ordinary variables and constraints with the usual JuMP macros.
Logical variables use the [`Logical`](@ref) variable type, and we assign a
constraint to a disjunct by tagging it with [`Disjunct`](@ref):

```jldoctest gdp_model
julia> @variable(model, 0 <= production <= 20);

julia> @variable(model, 0 <= cost <= 100);

julia> @variable(model, Y[1:2], Logical);

julia> @constraint(model, production <= 12, Disjunct(Y[1]));

julia> @constraint(model, cost >= 5 + 2 * production, Disjunct(Y[1]));

julia> @constraint(model, production <= 20, Disjunct(Y[2]));

julia> @constraint(model, cost >= 12 + production, Disjunct(Y[2]));

julia> @disjunction(model, Y);
```

Constraints that hold no matter which disjunct we choose are added without a
`Disjunct` tag, in the normal way:

```jldoctest gdp_model
julia> @constraint(model, demand, production >= 10);

julia> @objective(model, Min, cost);
```

To solve, we choose a reformulation. The `gdp_method` keyword of `optimize!`
selects one, and defaults to [`BigM`](@ref):

```jldoctest gdp_model
julia> optimize!(model, gdp_method = BigM())

julia> objective_value(model)
22.0

julia> value(production)
10.0
```

Note that `value` applied to a logical variable gives us a `Bool`, not a
floating-point number, so we can read the selected disjunct off directly:

```jldoctest gdp_model
julia> value(Y[1]), value(Y[2])
(false, true)
```

!!! note
    Every reformulation needs an optimizer, and some need one to solve auxiliary
    subproblems as well. [`MBM`](@ref) and [`CuttingPlanes`](@ref) both take an
    optimizer as their first argument for exactly this reason.

A GDP model can also be built over a continuous domain, so that a disjunction is
decided over time, space, or an uncertain parameter rather than once for the
whole problem. That requires `InfiniteOpt` and is covered in
[Infinite GDP Models](@ref infinite_guide).

## How a GDP Model is Stored

A `GDPModel` is a JuMP `Model` with a [`GDPData`](@ref) object attached to its
extension dictionary. That object records the logical variables, the disjunct
constraints grouped by their indicator, the disjunctions, and the logical
constraints, along with the mappings produced during reformulation. Those
mappings are what let us query a solved model in terms of the original logical
variables rather than the binary variables that replaced them.

Reformulation adds variables and constraints to the same model object, so it
runs at most once for a given method. The model records which method was applied
and whether it is still current, and repeating an `optimize!` call with the same
method reuses the existing reformulation instead of rebuilding it.

!!! note
    Reformulation mutates the model in place, but it is not cumulative. Passing
    a different method to a later `optimize!` call discards the previous
    reformulation and rebuilds from the original GDP structure, so we can solve
    one model with several methods in turn and compare them directly.

## Queries

We reach the attached data with [`gdp_data`](@ref), and [`is_gdp_model`](@ref)
tells us whether a given JuMP model carries it:

```jldoctest gdp_model
julia> is_gdp_model(model)
true
```

Since the model is an ordinary mixed-integer program after reformulation, all
the standard JuMP result queries apply unchanged:

```jldoctest gdp_model
julia> termination_status(model)
OPTIMAL::TerminationStatusCode = 1
```

## Modification

We can reformulate explicitly, without solving, using
[`reformulate_model`](@ref). This is how we inspect the mixed-integer program a
method produces:

```jldoctest gdp_model
julia> inspection = GDPModel();

julia> @variable(inspection, 0 <= x <= 20);

julia> @variable(inspection, W[1:2], Logical);

julia> @constraint(inspection, x <= 5, Disjunct(W[1]));

julia> @constraint(inspection, x >= 15, Disjunct(W[2]));

julia> @disjunction(inspection, W);

julia> reformulate_model(inspection, BigM())

julia> num_variables(inspection)
3
```

Reformulating the same model with [`Hull`](@ref) gives a larger but tighter
program, because each variable appearing in a disjunct is disaggregated into one
copy per disjunct:

```jldoctest gdp_model
julia> reformulate_model(inspection, Hull())

julia> num_variables(inspection)
5
```
