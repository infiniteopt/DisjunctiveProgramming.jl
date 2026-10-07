```@meta
DocTestFilters = [r"≤|<=", r"≥|>=", r" == | = ", r" ∈ | in ",
                  r"MathOptInterface|MOI"]
```

# [Disjunctions](@id constraints_guide)

A guide for disjunct constraints and disjunctions. See the respective
[technical manual](@ref constraints_manual) for more details.

## Overview

A *disjunct constraint* is an ordinary algebraic constraint that is enforced
only when its associated logical variable is true. A *disjunction* is a group of
logical variables among which exactly one may be selected, so that exactly one
group of disjunct constraints is enforced.

We declare the two separately. First we tag constraints with the logical
variable that governs them, then we declare the disjunction over those logical
variables. Nothing stops a logical variable from carrying constraints without
ever appearing in a disjunction, which is how we express a conditional
constraint that is not part of an either-or choice.

## Basic Usage

### Disjunct Constraints

A constraint becomes a disjunct constraint when we pass a [`Disjunct`](@ref) tag
naming its logical variable to `@constraint`. We can tag any constraint JuMP
accepts, including nonlinear and vector constraints:

```jldoctest gdp_cons; setup = :(using DisjunctiveProgramming, HiGHS)
julia> model = GDPModel(HiGHS.Optimizer);

julia> set_silent(model)

julia> @variable(model, 0 <= x[1:2] <= 10);

julia> @variable(model, Y[1:2], Logical);

julia> @constraint(model, x[1] + x[2] <= 8, Disjunct(Y[1]));

julia> @constraint(model, x[1] - x[2] >= 2, Disjunct(Y[1]));

julia> @constraint(model, x[1] + 3 * x[2] <= 12, Disjunct(Y[2]));
```

The tag comes last, after the constraint expression. Named and containerized
constraints follow JuMP's usual syntax, with the name or index expression
preceding the constraint:

```jldoctest gdp_cons
julia> @constraint(model, capacity[i = 1:2], x[i] <= 6, Disjunct(Y[1]));
```

!!! note
    [`BigM`](@ref) and [`Hull`](@ref) both support a quadratic or otherwise
    nonlinear disjunct constraint, but the resulting program is only as
    tractable as the underlying solver makes it. `Hull` additionally needs a
    perspective reformulation for nonlinear terms, controlled by its epsilon
    parameter.

### Declaring a Disjunction

[`@disjunction`](@ref) takes a vector of logical variables. Passing a container
directly is equivalent to passing its elements:

```jldoctest gdp_cons
julia> @disjunction(model, Y);
```

We can name a disjunction, in which case it is registered on the model and we
can retrieve it later:

```jldoctest gdp_cons
julia> named = GDPModel();

julia> @variable(named, 0 <= z <= 10);

julia> @variable(named, W[1:2], Logical);

julia> @constraint(named, z <= 3, Disjunct(W[1]));

julia> @constraint(named, z >= 7, Disjunct(W[2]));

julia> @disjunction(named, choice, W);

julia> named[:choice]
choice : [W[1] --> {z <= 3}] or [W[2] --> {z >= 7}]
```

The function form [`disjunction`](@ref) does the same without a macro, which is
convenient when we build disjunctions programmatically:

```jldoctest gdp_cons
julia> programmatic = GDPModel();

julia> @variable(programmatic, 0 <= w <= 10);

julia> @variable(programmatic, V[1:2], Logical);

julia> @constraint(programmatic, w <= 3, Disjunct(V[1]));

julia> @constraint(programmatic, w >= 7, Disjunct(V[2]));

julia> disjunction(programmatic, V);
```

We can declare several disjunctions in one block with [`@disjunctions`](@ref):

```jldoctest gdp_cons
julia> several = GDPModel();

julia> @variable(several, 0 <= v <= 10);

julia> @variable(several, Z[1:2, 1:2], Logical);

julia> for i in 1:2, j in 1:2
           @constraint(several, v <= i + j, Disjunct(Z[i, j]))
       end

julia> @disjunctions(several, begin
           Z[1, :]
           Z[2, :]
       end);
```

### Exclusivity

By default a disjunction adds a constraint requiring that exactly one of its
disjuncts be selected. The `exactly1` keyword relaxes this and permits any
number of disjuncts to be active, which we occasionally want when the
disjunction encodes a set of independently available options:

```jldoctest gdp_cons
julia> relaxed = GDPModel();

julia> @variable(relaxed, 0 <= u <= 10);

julia> @variable(relaxed, R[1:2], Logical);

julia> @constraint(relaxed, u <= 3, Disjunct(R[1]));

julia> @constraint(relaxed, u <= 7, Disjunct(R[2]));

julia> @disjunction(relaxed, R, exactly1 = false);
```

!!! warning
    Some reformulations rely on the exclusivity constraint for correctness or
    for tightness. Set `exactly1 = false` only when the modeling intent
    genuinely permits several disjuncts at once.

### Empty Disjuncts

A disjunct need not carry any constraints. An empty disjunct represents the
alternative of imposing nothing beyond the global constraints, which is how we
model an optional requirement. Here the second disjunct is empty, so selecting
it leaves `x` bounded only by its global bounds:

```jldoctest gdp_cons
julia> optional = GDPModel(HiGHS.Optimizer);

julia> set_silent(optional)

julia> @variable(optional, 0 <= q <= 10);

julia> @variable(optional, O[1:2], Logical);

julia> @constraint(optional, q <= 3, Disjunct(O[1]));

julia> @disjunction(optional, O);

julia> @objective(optional, Max, q);

julia> optimize!(optional, gdp_method = BigM())

julia> objective_value(optional)
10.0
```

## Nested Disjunctions

A disjunction can itself sit inside a disjunct, giving us a hierarchy of
decisions. We do this by passing a `Disjunct` tag to `@disjunction`, exactly as
we would for a constraint. The inner disjunction is then enforced only when the
outer disjunct is selected:

```jldoctest gdp_cons
julia> nested = GDPModel(HiGHS.Optimizer);

julia> set_silent(nested)

julia> @variable(nested, 0 <= capacity <= 500);

julia> @variable(nested, build, Logical);

julia> @variable(nested, outsource, Logical, logical_complement = build);

julia> @variable(nested, size_choice[1:2], Logical);

julia> @constraint(nested, capacity <= 100, Disjunct(size_choice[1]));

julia> @constraint(nested, capacity <= 500, Disjunct(size_choice[2]));

julia> @constraint(nested, capacity <= 50, Disjunct(outsource));

julia> @disjunction(nested, inner, size_choice, Disjunct(build));

julia> @disjunction(nested, [build, outsource]);

julia> @objective(nested, Max, capacity);

julia> optimize!(nested, gdp_method = BigM())

julia> value(build), value(capacity)
(true, 500.0)
```

Notice that we declare the inner disjunction before the outer one. The logical
variables of the inner disjunction carry constraints of their own, and the outer
disjunction governs whether that whole sub-decision is active.

The exclusivity constraint added for a nested disjunction is conditional on its
parent rather than absolute. For an inner disjunction over `W` sitting inside
disjunct `P[1]`, the constraint added is equivalent to `W in Exactly(P[1])`.
Exactly one variable in `W` is true when `P[1]` is true, and every variable in
`W` is false when `P[1]` is false, meaning the parent disjunct was not selected
and its sub-decision does not arise.
