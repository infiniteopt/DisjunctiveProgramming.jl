```@meta
DocTestFilters = [r"≤|<=", r"≥|>=", r" == | = ", r" ∈ | in ",
                  r"MathOptInterface|MOI"]
```

# [Quick Start Guide](@id quick_start)

A short walkthrough that builds, reformulates, and solves a complete GDP model.

## Overview

We will model a problem where a point must lie in one of two disjoint boxes, and
we want to push it as far out as we can. The example comes from the
[Cornell University Computational Optimization Open Textbook](https://optimization.cbe.cornell.edu/index.php?title=Disjunctive_inequalities).

Written as a disjunction, the problem is

```math
\max \ x_1 + x_2 \quad \text{s.t.} \quad
\begin{bmatrix} 2 \leq x_1 \leq 6 \ 5 \leq x_2 \leq 9 \end{bmatrix}
\ \vee \
\begin{bmatrix} 8 \leq x_1 \leq 11 \ 10 \leq x_2 \leq 15 \end{bmatrix},
\quad 0 \leq x \leq 20.
```

The two boxes do not overlap, so this is a genuine either-or choice rather than
something we could write with ordinary algebraic constraints.

## Model Definition

Let's start by creating a [`GDPModel`](@ref) with an optimizer attached:

```jldoctest quick; setup = :(using DisjunctiveProgramming, HiGHS)
julia> model = GDPModel(HiGHS.Optimizer);

julia> set_silent(model)
```

Next we add the continuous variables and one [`Logical`](@ref) variable per
disjunct. The logical variables record which box we select:

```jldoctest quick
julia> @variable(model, 0 <= x[1:2] <= 20);

julia> @variable(model, Y[1:2], Logical);
```

Now we attach the box constraints to their disjuncts with the
[`Disjunct`](@ref) tag, and declare the disjunction over the two logical
variables:

```jldoctest quick
julia> @constraint(model, [i = 1:2], [2, 5][i] <= x[i] <= [6, 9][i], Disjunct(Y[1]));

julia> @constraint(model, [i = 1:2], [8, 10][i] <= x[i] <= [11, 15][i], Disjunct(Y[2]));

julia> @disjunction(model, Y);

julia> @objective(model, Max, sum(x));
```

At this point the model still holds the disjunction as disjunctive structure. No
binary variable exists yet:

```jldoctest quick
julia> num_variables(model)
4
```

## Solution and Queries

We solve by choosing a reformulation. Let's start with [`BigM`](@ref), fixing
the value at 100 and disabling the automatic tightening so we can see exactly
what the encoding produces:

```jldoctest quick
julia> optimize!(model, gdp_method = BigM(100, false))

julia> objective_value(model)
26.0
```

The solution puts us in the second box, which we read straight off the logical
variables:

```jldoctest quick
julia> value.(x)
2-element Vector{Float64}:
 11.0
 15.0

julia> value.(Y)
2-element BitVector:
 0
 1
```

Reformulation rewrote the model in place, so we can print it to see the
mixed-integer program that the solver actually received:

```jldoctest quick
julia> print(model)
Max x[1] + x[2]
Subject to
 Y[1] + Y[2] = 1
 x[1] - 100 Y[1] ≥ -98
 x[2] - 100 Y[1] ≥ -95
 x[1] - 100 Y[2] ≥ -92
 x[2] - 100 Y[2] ≥ -90
 x[1] + 100 Y[1] ≤ 106
 x[2] + 100 Y[1] ≤ 109
 x[1] + 100 Y[2] ≤ 111
 x[2] + 100 Y[2] ≤ 115
 x[1] ≥ 0
 x[2] ≥ 0
 x[1] ≤ 20
 x[2] ≤ 20
 Y[1] binary
 Y[2] binary
```

Passing a different method discards that reformulation and builds a new one, so
we can compare encodings on the same model. [`Hull`](@ref) disaggregates each
variable into one copy per disjunct, giving a larger program with a tighter
relaxation:

```jldoctest quick
julia> optimize!(model, gdp_method = Hull())

julia> objective_value(model)
26.0

julia> num_variables(model)
8
```

Both methods agree on the answer, as they must. They differ in the size of the
program and in how quickly a solver reaches that answer, which is the whole
reason we get to choose.

!!! tip
    See [Solution Methods](@ref methods_guide) for the other four
    reformulations, including two that compute tighter big-M coefficients by
    solving auxiliary subproblems.

## Summary Script

Here is the whole model in one piece:

```julia
using DisjunctiveProgramming, HiGHS

model = GDPModel(HiGHS.Optimizer)
set_silent(model)

@variable(model, 0 <= x[1:2] <= 20)
@variable(model, Y[1:2], Logical)

@constraint(model, [i = 1:2], [2, 5][i] <= x[i] <= [6, 9][i], Disjunct(Y[1]))
@constraint(model, [i = 1:2], [8, 10][i] <= x[i] <= [11, 15][i], Disjunct(Y[2]))
@disjunction(model, Y)

@objective(model, Max, sum(x))
optimize!(model, gdp_method = BigM(100, false))

println("objective = ", objective_value(model))
println("x         = ", value.(x))
println("selected  = ", value.(Y))
```

## What Next

- [GDP Models](@ref model_guide) covers model construction and result queries in
  full.
- [Logical Constraints](@ref logic_guide) covers propositions and cardinality
  requirements, which this example did not need.
- [Disjunctions](@ref constraints_guide) covers nesting and the exclusivity
  keyword.
- [Solution Methods](@ref methods_guide) covers the reformulations and how they
  trade formulation size against relaxation strength.
- [Infinite GDP Models](@ref infinite_guide) covers disjunctions decided over a
  continuous domain such as time or uncertainty.
