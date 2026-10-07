```@meta
DocTestFilters = [r"≤|<=", r"≥|>=", r" == | = ", r" ∈ | in ",
                  r"MathOptInterface|MOI"]
```

# [Infinite GDP Models](@id infinite_guide)

A guide for disjunctive modeling over continuous domains through
[InfiniteOpt.jl](https://github.com/infiniteopt/InfiniteOpt.jl). See the
respective [technical manual](@ref infinite_manual) for more details.

## Overview

`InfiniteOpt` models decisions that live over a continuous domain: time in a
dynamic problem, space in a distributed one, or a random parameter in a
stochastic one. Loading it alongside `DisjunctiveProgramming` enables an
extension that brings the two together, so a disjunction can be decided over
that domain rather than once for the whole problem. A process that switches
operating mode as demand grows, or a design whose active constraints depend on
the realization of an uncertain parameter, is a disjunction indexed by an
infinite parameter.

The pieces mirror the finite ones. An [`InfiniteGDPModel`](@ref) replaces
[`GDPModel`](@ref), and [`InfiniteLogical`](@ref) replaces [`Logical`](@ref)
for a Boolean decision that varies over the domain. Everything else, disjunct
constraints, disjunctions, logical constraints, and the reformulation methods,
is used exactly as on a finite model.

!!! note
    The extension loads automatically once `InfiniteOpt` is imported, so
    `InfiniteGDPModel` and `InfiniteLogical` are only defined after
    `using InfiniteOpt`.

## Basic Usage

Let's model a process that meets a demand growing over a horizon. It can run in
a cheap mode capped at 12 units, or in an expensive mode that reaches 20. We
build the model with [`InfiniteGDPModel`](@ref) and declare the horizon as an
infinite parameter:

```jldoctest gdp_infinite; setup = :(using DisjunctiveProgramming, InfiniteOpt, HiGHS)
julia> model = InfiniteGDPModel(HiGHS.Optimizer);

julia> set_silent(model)

julia> @infinite_parameter(model, t in [0, 1], num_supports = 5);
```

Variables that vary over the horizon carry `Infinite(t)`, and the logical
variables that choose the mode carry [`InfiniteLogical`](@ref) over the same
parameter:

```jldoctest gdp_infinite
julia> @variable(model, 0 <= production <= 20, Infinite(t));

julia> @variable(model, 0 <= cost <= 100, Infinite(t));

julia> @variable(model, Y[1:2], InfiniteLogical(t));
```

The disjunct constraints and the disjunction are written exactly as on a finite
model. Each one holds at every point of the horizon:

```jldoctest gdp_infinite
julia> @constraint(model, production <= 12, Disjunct(Y[1]));

julia> @constraint(model, cost >= 2 + production, Disjunct(Y[1]));

julia> @constraint(model, production <= 20, Disjunct(Y[2]));

julia> @constraint(model, cost >= 8 + production, Disjunct(Y[2]));

julia> @disjunction(model, Y);

julia> @constraint(model, production >= 10 + 5 * t);

julia> @objective(model, Min, integral(cost, t));
```

Solving works as before, and we choose the method with the same `gdp_method`
keyword:

```jldoctest gdp_infinite
julia> optimize!(model, gdp_method = BigM())

julia> objective_value(model)
18.25
```

## Reading a Solution

An infinite logical variable is decided once per support, so `value` gives us a
vector of Booleans rather than a single one, aligned with the supports of its
infinite parameter:

```jldoctest gdp_infinite
julia> supports(t)
5-element Vector{Float64}:
 0.0
 0.25
 0.5
 0.75
 1.0

julia> value(Y[1])
5-element BitVector:
 1
 1
 0
 0
 0

julia> value(Y[2])
5-element BitVector:
 0
 0
 1
 1
 1
```

The cheap mode is selected while demand stays within its capacity, and the
process switches to the expensive mode once demand outgrows it:

```jldoctest gdp_infinite
julia> value(production)
5-element Vector{Float64}:
 10.0
 11.25
 12.5
 13.75
 15.0

julia> value(cost)
5-element Vector{Float64}:
 12.0
 13.25
 20.5
 21.75
 23.0
```

## Choosing Once or Choosing Over the Domain

A plain [`Logical`](@ref) variable in an infinite model is a decision made once
for the entire domain, while an [`InfiniteLogical`](@ref) one is remade at every
support. The distinction is a modeling choice, not a technicality: a mode that
can be switched during operation is infinite, and a piece of equipment selected
at the design stage is not.

Building the same model with finite logical variables forces one mode across the
whole horizon, and the expensive mode is then the only feasible choice:

```jldoctest gdp_infinite
julia> fixed = InfiniteGDPModel(HiGHS.Optimizer);

julia> set_silent(fixed)

julia> @infinite_parameter(fixed, s in [0, 1], num_supports = 5);

julia> @variable(fixed, 0 <= output <= 20, Infinite(s));

julia> @variable(fixed, 0 <= expense <= 100, Infinite(s));

julia> @variable(fixed, Z[1:2], Logical);

julia> @constraint(fixed, output <= 12, Disjunct(Z[1]));

julia> @constraint(fixed, expense >= 2 + output, Disjunct(Z[1]));

julia> @constraint(fixed, output <= 20, Disjunct(Z[2]));

julia> @constraint(fixed, expense >= 8 + output, Disjunct(Z[2]));

julia> @disjunction(fixed, Z);

julia> @constraint(fixed, output >= 10 + 5 * s);

julia> @objective(fixed, Min, integral(expense, s));

julia> optimize!(fixed, gdp_method = BigM())

julia> objective_value(fixed)
20.5

julia> value.(Z)
2-element BitVector:
 0
 1
```

The gap between the two objective values is what the ability to switch modes is
worth, which is the kind of question this model answers.

## How Reformulation Works Here

Reformulation runs on the infinite model, before transcription. The disjunct
constraints are rewritten symbolically, in terms of the infinite variables, and
`InfiniteOpt` then transcribes the reformulated model over the supports in the
usual way. Two consequences are worth keeping in mind.

An infinite logical variable becomes one binary per support, so the size of the
mixed-integer program grows with the support count as well as with the number of
disjuncts. A support count chosen for accuracy in a continuous model may be far
more than the disjunctive part of the model needs.

Because reformulation happens before transcription, everything it produces is an
ordinary `InfiniteOpt` object. Derivatives, measures, and parameter functions
appearing in a disjunct constraint are carried through unchanged.

## Solution Methods

Every method in [Solution Methods](@ref methods_guide) applies to an infinite
model. Two of them do extra work to account for the infinite domain.

[`MBM`](@ref) solves its subproblem at every support. When the resulting values
agree across supports it uses a single big-M, and when they differ it builds a
parameter function of the infinite parameters, giving each support the tightest
value that is valid there rather than the largest value over the whole domain.

[`CuttingPlanes`](@ref) weights its separation problem and its cuts by
quadrature weights read from the measure in the objective. A cut then
approximates the integral the objective takes, rather than a plain sum over
supports, which matters whenever supports are unevenly spaced or carry unequal
quadrature coefficients. When the objective does not measure a given parameter,
trapezoid weights are used for a scalar parameter over an interval domain and a
uniform average otherwise. A variable that does not depend on an infinite
parameter carries a weight of one.

The methods agree on the optimum for our model, as they must:

```jldoctest gdp_infinite
julia> optimize!(model, gdp_method = Hull())

julia> objective_value(model)
18.25

julia> optimize!(model, gdp_method = MBM(HiGHS.Optimizer))

julia> objective_value(model)
18.25

julia> optimize!(model, gdp_method = CuttingPlanes(HiGHS.Optimizer))

julia> objective_value(model)
18.25
```

[`Direct`](@ref) applies as well. Each disjunction is lowered to one constraint
in a [`DisjunctionSet`](@ref) on the infinite model, and transcription writes it
out per support for the solver to consume.

!!! note
    [`MBM`](@ref) and [`CuttingPlanes`](@ref) copy the infinite model to build
    their subproblems, which needs `JuMP.copy_model` for an `InfiniteModel`.
    That method is available from `InfiniteOpt` v0.6.3 onwards.
