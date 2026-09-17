```@meta
DocTestFilters = [r"≤|<=", r"≥|>=", r" == | = ", r" ∈ | in ",
                  r"MathOptInterface|MOI"]
```

# [Solution Methods](@id methods_guide)

A guide for the reformulations that turn a GDP model into a mixed-integer
program. See the respective [technical manual](@ref methods_manual) for more
details.

## Overview

We do not solve a `GDPModel` directly. Before a solver sees it, the disjunctions
and logical constraints are replaced by algebraic constraints on binary
variables, producing an ordinary mixed-integer program. We choose the method
that performs this replacement, and the choice matters. Different reformulations
of the same model agree on the integer solutions but differ sharply in the
strength of their continuous relaxation, and therefore in how long a
branch-and-bound solver takes.

Let's define a small model that we can reuse for every method. It chooses
between two production processes to meet a demand at least cost:

```jldoctest gdp_methods; setup = :(using DisjunctiveProgramming, HiGHS)
julia> model = GDPModel(HiGHS.Optimizer);

julia> set_silent(model)

julia> @variable(model, 0 <= production <= 20);

julia> @variable(model, 0 <= cost <= 100);

julia> @variable(model, Y[1:2], Logical);

julia> @constraint(model, production <= 12, Disjunct(Y[1]));

julia> @constraint(model, cost >= 5 + 2 * production, Disjunct(Y[1]));

julia> @constraint(model, production <= 20, Disjunct(Y[2]));

julia> @constraint(model, cost >= 12 + production, Disjunct(Y[2]));

julia> @disjunction(model, Y);

julia> @constraint(model, production >= 10);

julia> @objective(model, Min, cost);
```

We pass the method through the `gdp_method` keyword of `optimize!`:

```jldoctest gdp_methods
julia> optimize!(model, gdp_method = BigM())

julia> objective_value(model)
22.0
```

Passing a different method to the same model discards the previous
reformulation and applies the new one, so we reuse this model for every example
below and compare each method on identical input.

We have seven methods available.

| Method | Extra solver needed | Relaxation strength | Program size |
|---|---|---|---|
| [`BigM`](@ref) | no | weakest | smallest |
| [`MBM`](@ref) | yes | tighter than `BigM` | same as `BigM` |
| [`PSplit`](@ref) | no | between `BigM` and `Hull` | tunable |
| [`Hull`](@ref) | no | tightest of the algebraic methods | largest |
| [`CuttingPlanes`](@ref) | yes | strengthens a base method | grows with iterations |
| [`Indicator`](@ref) | no, but solver must support it | solver-dependent | smallest |
| [`Direct`](@ref) | no, but solver must support `DisjunctionSet` | set by the solver | disjunctions passed through |

Every one of them applies to a model built over a continuous domain as well,
where [`MBM`](@ref) and [`CuttingPlanes`](@ref) additionally adapt to the
supports. See [Infinite GDP Models](@ref infinite_guide).

!!! tip
    Start with `BigM` while building a model. It is the cheapest to construct
    and the easiest to read when printed. Move to `Hull` or `MBM` once the model
    is correct and solve time becomes the constraint.

## Big-M

The big-M reformulation relaxes each disjunct constraint by an amount large
enough to make it vacuous when its disjunct is not selected. For a constraint
``r(x) \leq 0`` governed by indicator ``Y`` with binary ``y``, we get
``r(x) \leq M(1 - y)``.

The method takes the value of ``M`` and a flag controlling whether we derive
tighter values from the variable bounds:

```jldoctest gdp_methods
julia> optimize!(model, gdp_method = BigM(1e4))

julia> objective_value(model)
22.0
```

By default the method tightens the supplied value using the bounds of the
variables appearing in each constraint. We can disable tightening, which is
occasionally useful for reproducing a specific formulation:

```jldoctest gdp_methods
julia> optimize!(model, gdp_method = BigM(1e4, false))

julia> objective_value(model)
22.0
```

!!! warning
    A big-M value that is too small silently removes valid solutions, and one
    that is far too large gives a relaxation so weak that branch and bound makes
    little progress. Bound every variable that appears in a disjunct constraint
    so that tightening has something to work with.

## Multiple Big-M

Big-M applies one value per constraint. Multiple big-M computes a separate value
for each constraint-disjunct pair, by maximizing the constraint's left-hand side
over the region defined by the *other* disjunct. The values we get are no weaker
than a single big-M and usually a good deal tighter, at the cost of solving one
small optimization problem per pair.

Since we have to solve those subproblems, the method requires an optimizer:

```jldoctest gdp_methods
julia> optimize!(model, gdp_method = MBM(HiGHS.Optimizer))

julia> objective_value(model)
22.0
```

A fallback value is used for any pair whose subproblem does not yield a finite
bound, and we set it as the second argument:

```jldoctest gdp_methods
julia> optimize!(model, gdp_method = MBM(HiGHS.Optimizer, 1e6))

julia> objective_value(model)
22.0
```

The resulting program has the same number of variables and constraints as the
big-M program. The improvement is entirely in the coefficients, which makes this
an inexpensive substitution wherever we would otherwise use big-M.

## Convex Hull

The hull reformulation disaggregates every variable appearing in a disjunction
into one copy per disjunct, links the copies to the original by a summation
constraint, and scales each disjunct's constraints by its binary variable. For
disjuncts described by convex constraints, the continuous relaxation we get is
the convex hull of the disjunction, which is the tightest relaxation available.
For nonconvex disjuncts we get the hull of the convexified disjuncts, which is
still far tighter than big-M but no longer exact.

```jldoctest gdp_methods
julia> optimize!(model, gdp_method = Hull())

julia> objective_value(model)
22.0
```

The price is size. Let's compare the two programs directly:

```jldoctest gdp_methods
julia> optimize!(model, gdp_method = BigM());

julia> big_m_size = num_variables(model)
4

julia> optimize!(model, gdp_method = Hull());

julia> num_variables(model)
8
```

Nonlinear disjunct constraints need a perspective function, which is singular
when the binary variable is zero. The method's parameter is the epsilon we use
to regularize it:

```jldoctest gdp_methods
julia> optimize!(model, gdp_method = Hull(1e-8))

julia> objective_value(model)
22.0
```

!!! note
    A smaller epsilon gives a more faithful perspective reformulation but a
    worse-conditioned problem. The default of `1e-6` is a reasonable compromise
    for most models, and only needs revisiting when a nonlinear solver reports
    numerical trouble.

## P-Split

P-split sits between big-M and hull. Rather than disaggregating every variable,
it partitions the variables into groups and disaggregates at the level of
groups. The number of groups is our dial between formulation strength and
formulation size: more groups give a stronger relaxation and a larger program.

We know both ends of that dial. A single group gives a formulation whose
continuous relaxation admits the same set of feasible original variables as
big-M. Splitting on every variable gives the convex hull of the disjunction,
provided the disjunct constraints are affine and every variable is bounded.

!!! note
    The hull guarantee at the finest partition holds for affine disjunct
    constraints over a bounded box. When a disjunct contains nonlinear
    constraints, no P-split formulation is guaranteed to recover the true convex
    hull of the disjunction, though finer partitions still tighten the
    relaxation.

We can give the partition explicitly as a vector of variable vectors:

```jldoctest gdp_methods
julia> partition = [[model[:production]], [model[:cost]]];

julia> optimize!(model, gdp_method = PSplit(partition))

julia> objective_value(model)
22.0
```

Alternatively we give a number of groups and let the variables be divided among
them automatically. Note that this form inspects the model at the moment we
construct the method, so we build a fresh model here rather than reusing one
that already carries the variables an earlier reformulation added:

```jldoctest gdp_methods
julia> auto = GDPModel(HiGHS.Optimizer);

julia> set_silent(auto)

julia> @variable(auto, 0 <= p <= 20);

julia> @variable(auto, 0 <= c <= 100);

julia> @variable(auto, S[1:2], Logical);

julia> @constraint(auto, p <= 12, Disjunct(S[1]));

julia> @constraint(auto, c >= 5 + 2 * p, Disjunct(S[1]));

julia> @constraint(auto, p <= 20, Disjunct(S[2]));

julia> @constraint(auto, c >= 12 + p, Disjunct(S[2]));

julia> @disjunction(auto, S);

julia> @constraint(auto, p >= 10);

julia> @objective(auto, Min, c);

julia> optimize!(auto, gdp_method = PSplit(2, auto))

julia> objective_value(auto)
22.0
```

!!! warning
    `PSplit(n, model)` partitions every variable the model currently holds. If
    the model has already been reformulated, that includes the auxiliary
    variables the previous reformulation created, and the partition will not be
    the one we intended. Construct it from a model that still holds only our own
    variables, or pass an explicit partition.

## Cutting Planes

The cutting planes method does not produce a formulation on its own. It solves a
sequence of separation problems, each of which yields a cut that tightens the
relaxation, and then applies a final reformulation to the strengthened model.
The cuts are valid for the hull, so we approach hull strength while keeping a
program closer to big-M in size.

We need an optimizer for the separation problems:

!!! note
    The cutting planes examples below are shown rather than executed by the
    documentation build. The method copies the model internally, which currently
    emits a `JuMP` warning about an unsupported container copy, and that warning
    carries a machine-specific path that cannot be checked reproducibly.

```julia-repl
julia> optimize!(model, gdp_method = CuttingPlanes(HiGHS.Optimizer))

julia> objective_value(model)
22.0
```

We can adjust the number of separation rounds, the tolerance below which a cut
is considered unhelpful, the reformulation applied at the end, and the big-M
value of the relaxed big-M model the loop cuts against:

```julia-repl
julia> method = CuttingPlanes(HiGHS.Optimizer; max_iter = 10,
                              seperation_tolerance = 1e-8,
                              final_reform_method = BigM(), M_value = 1e5);

julia> optimize!(model, gdp_method = method)

julia> objective_value(model)
22.0
```

!!! note
    Each round adds constraints permanently to the model, so a large `max_iter`
    trades a tighter relaxation for a larger program and a longer setup time.
    The default of three rounds captures most of the available tightening on
    typical models.

## Indicator Constraints

Rather than encoding the disjunction algebraically, this method passes it to the
solver as indicator constraints and leaves the solver to handle the implication
internally. Modern mixed-integer solvers implement these natively and can often
propagate them more effectively than any big-M encoding.

```jldoctest gdp_methods
julia> optimize!(model, gdp_method = Indicator())

julia> objective_value(model)
22.0
```

!!! warning
    Indicator constraints are supported only for linear disjunct constraints,
    and only by solvers that implement them. A solver without support rejects
    the model rather than falling back to another encoding.

## Direct Lowering

Every method above encodes the disjunction in algebra that an ordinary
mixed-integer solver understands. [`Direct`](@ref) does not encode it at all.
Each disjunction becomes a single vector constraint in a
[`DisjunctionSet`](@ref), so the disjunctive structure reaches the solver
intact and the solver decides what to do with it, whether that is a
reformulation of its own or an algorithm that works on the disjunctions
directly, such as logic-based outer approximation.

The model therefore needs an optimizer that supports the set, such as the one
provided by
[DisjunctiveAlgorithms.jl](https://github.com/infiniteopt/DisjunctiveAlgorithms.jl):

```julia-repl
julia> using DisjunctiveAlgorithms, Ipopt

julia> solver_model = GDPModel(() -> DisjunctiveAlgorithms.Optimizer(
           Ipopt.Optimizer, HiGHS.Optimizer));

julia> optimize!(solver_model, gdp_method = Direct())
```

To see what the method produces we can reformulate a model that has no
optimizer attached, which leaves the lowered constraint in the model for us to
read:

```jldoctest gdp_direct; setup = :(using DisjunctiveProgramming)
julia> direct = GDPModel();

julia> @variable(direct, 0 <= production <= 20);

julia> @variable(direct, 0 <= cost <= 100);

julia> @variable(direct, Y[1:2], Logical);

julia> @constraint(direct, production <= 12, Disjunct(Y[1]));

julia> @constraint(direct, cost >= 5 + 2 * production, Disjunct(Y[1]));

julia> @constraint(direct, production <= 20, Disjunct(Y[2]));

julia> @constraint(direct, cost >= 12 + production, Disjunct(Y[2]));

julia> @disjunction(direct, Y);

julia> @objective(direct, Min, cost);

julia> reformulate_model(direct, Direct())

julia> con = constraint_object(
           all_constraints(direct, Vector{AffExpr}, DisjunctionSet)[1]);

julia> con.func
7-element Vector{AffExpr}:
 1
 Y[1]
 Y[2]
 production
 -2 production + cost
 production
 -production + cost
```

The function stacks the disjunction's activation expression, one indicator per
disjunct, and then the constraint rows of each disjunct in order. The set knows
where each piece sits:

```jldoctest gdp_direct
julia> num_disjuncts(con.set)
2

julia> activation_index(con.set), indicator_indices(con.set)
(1, 2:3)

julia> row_indices(con.set, 1), row_indices(con.set, 2)
(4:5, 6:7)
```

A top-level disjunction has the constant activation `1`, so exactly one of its
disjuncts is selected. A nested disjunction instead carries the indicator of its
parent disjunct as the activation, so it selects one of its own disjuncts while
the parent is selected and is vacuous otherwise.

!!! note
    `Direct` requires every disjunction to select exactly one disjunct, and a
    nested disjunction must have been created with `exactly1 = true`.

## Reformulating Without Solving

[`reformulate_model`](@ref) applies a method and stops, which is how we inspect
or export the mixed-integer program a method produces:

```jldoctest gdp_methods
julia> reformulate_model(model, BigM())

julia> num_variables(model)
12
```

Once reformulated, the model is an ordinary JuMP model and every JuMP facility
applies to it, including `write_to_file` for exporting and `print` for reading
the formulation directly.
