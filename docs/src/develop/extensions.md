```@meta
DocTestFilters = [r"≤|<=", r"≥|>=", r" == | = ", r" ∈ | in ",
                  r"MathOptInterface|MOI"]
```

# [Extensions](@id extensions)

A guide for extending `DisjunctiveProgramming` with new reformulation methods
and new model types.

## Overview

The package separates the modeling layer from the encoding, and that separation
is the extension point. A `GDPModel` stores disjunctions as disjunctive
structure. A *reformulation method* is a type that says how that structure
becomes algebra. Adding one means defining a type and telling the package how to
rewrite a single disjunct constraint.

Everything else is handled for us. The package walks the disjunctions, resolves
nesting, converts logical constraints to conjunctive normal form, creates the
binary variable for each logical variable, and records the mappings that let a
solved model be queried in terms of the original logical variables. Our method
only needs to answer one question: given a constraint and the binary variable
that governs it, what constraints should replace it?

## Adding a Reformulation Method

A method is any subtype of [`AbstractReformulationMethod`](@ref). Fields hold
whatever parameters the method needs. Let's write a deliberately simple big-M
that applies a fixed value with no tightening:

```jldoctest extend; setup = :(using DisjunctiveProgramming, HiGHS)
julia> struct SimpleBigM <: DisjunctiveProgramming.AbstractReformulationMethod
           M::Float64
       end
```

Now we extend [`reformulate_disjunct_constraint`](@ref), which receives the
model, the constraint being reformulated, the binary variable governing it, and
our method. It returns a vector of replacement constraints. We dispatch on the
constraint's set to handle each sense:

```jldoctest extend
julia> function DisjunctiveProgramming.reformulate_disjunct_constraint(
           model::JuMP.AbstractModel,
           con::JuMP.ScalarConstraint{T, S},
           bvref::JuMP.AbstractVariableRef,
           method::SimpleBigM
       ) where {T, S <: MOI.LessThan}
           new_func = JuMP.@expression(model, con.func - method.M * (1 - bvref))
           return [JuMP.build_constraint(error, new_func, con.set)]
       end

julia> function DisjunctiveProgramming.reformulate_disjunct_constraint(
           model::JuMP.AbstractModel,
           con::JuMP.ScalarConstraint{T, S},
           bvref::JuMP.AbstractVariableRef,
           method::SimpleBigM
       ) where {T, S <: MOI.GreaterThan}
           new_func = JuMP.@expression(model, con.func + method.M * (1 - bvref))
           return [JuMP.build_constraint(error, new_func, con.set)]
       end
```

That is the whole method. We can now pass it to `optimize!` like any built-in
one:

```jldoctest extend
julia> model = GDPModel(HiGHS.Optimizer);

julia> set_silent(model)

julia> @variable(model, 0 <= x <= 20);

julia> @variable(model, Y[1:2], Logical);

julia> @constraint(model, x <= 5, Disjunct(Y[1]));

julia> @constraint(model, x >= 15, Disjunct(Y[2]));

julia> @disjunction(model, Y);

julia> @objective(model, Max, x);

julia> optimize!(model, gdp_method = SimpleBigM(100))

julia> objective_value(model)
20.0
```

!!! note
    A complete method should cover every constraint form the package supports:
    `MOI.LessThan`, `MOI.GreaterThan`, `MOI.EqualTo`, and `MOI.Interval` for
    scalar constraints, along with `MOI.Nonpositives`, `MOI.Nonnegatives`, and
    `MOI.Zeros` for vector constraints. Our example covers two of them, so it
    errors on anything else. See `src/bigm.jl` for a method that covers them all.

The binary argument arrives as a `JuMP.GenericAffExpr` rather than a variable
reference when the governing logical variable is a logical complement. A method
that supports complements needs a second set of methods dispatching on that
type, as `src/bigm.jl` and `src/indicator.jl` both do.

## Requiring Exclusivity

Some reformulations are only valid when exactly one disjunct is selected. We
declare that by extending [`requires_exactly1`](@ref), which defaults to
`false`:

```jldoctest extend
julia> DisjunctiveProgramming.requires_exactly1(::SimpleBigM) = true
```

The package then checks each disjunction before reformulating and raises an
informative error if a disjunction was built with `exactly1 = false` and its
indicators are not logical complements. [`Hull`](@ref) sets this to `true`.

## Requiring Variable Bounds

A method that needs bounds on the variables appearing in a disjunction declares
that by extending [`requires_variable_bound_info`](@ref) and supplying
[`set_variable_bound_info`](@ref). The package then collects the bounds before
reformulating, and our method reads them back with
[`variable_bound_info`](@ref):

```julia
DisjunctiveProgramming.requires_variable_bound_info(::MyMethod) = true

function DisjunctiveProgramming.set_variable_bound_info(vref, ::MyMethod)
    lower = JuMP.has_lower_bound(vref) ? JuMP.lower_bound(vref) : -Inf
    upper = JuMP.has_upper_bound(vref) ? JuMP.upper_bound(vref) : Inf
    return lower, upper
end
```

`set_variable_bound_info` returns a `(lower, upper)` tuple per variable. This is
the hook that lets a method compute tighter coefficients than the user supplied.
[`BigM`](@ref) requires bounds only when its `tighten` flag is set, which it
expresses by returning the flag itself rather than a constant.

## Reformulating a Whole Disjunction

Rewriting one constraint at a time is not always enough. [`Hull`](@ref) has to
disaggregate variables across the whole disjunction before it can touch any
individual constraint. A method in that situation extends
[`reformulate_disjunction`](@ref) instead, which receives the entire
[`Disjunction`](@ref) and returns all of its replacement constraints.

The default implementation walks the disjuncts and calls
`reformulate_disjunct_constraint` on each constraint, so overriding it means
taking responsibility for that walk, including nested disjunctions.

!!! tip
    Prefer extending `reformulate_disjunct_constraint`. Reach for
    `reformulate_disjunction` only when the method genuinely needs to see the
    whole disjunction at once, since the per-constraint hook composes with
    nesting and vector constraints for free.

## Supporting New Model Types

The reformulation functions dispatch on `JuMP.AbstractModel` rather than
`JuMP.Model`, so a package providing its own model type can support GDP modeling
by extending the same hooks. The InfiniteOpt extension in
`ext/InfiniteDisjunctiveProgramming.jl` is the worked example in this
repository, and what it provides to users is described in
[Infinite GDP Models](@ref infinite_guide).

Two principles keep such an extension small.

Overload the functions that already exist rather than building parallel
infrastructure. If the base package has a function that does the job for
`JuMP.Model`, extend that function for the new model type instead of writing a
differently named one.

Where behaviour genuinely has to differ per model type, add the dispatch point
in the base package rather than special-casing the extension inside it. The base
code should not know which extensions exist.

## Consuming Disjunctions in a Solver

A solver that implements its own disjunctive algorithm does not want a
reformulation at all. It wants the disjunctions. [`Direct`](@ref) is the method
that hands them over: every disjunction is lowered to one vector constraint in a
[`DisjunctionSet`](@ref), which is an ordinary `MOI.AbstractVectorSet` and so
travels through MOI like any other set.

The constraint function is a flat vector,
`[p, z_1, ..., z_k, rows of disjunct 1, ..., rows of disjunct k]`, holding the
activation expression `p`, one indicator expression per disjunct, and the rows
of each disjunct in order. A point is in the set when the indicators sum to the
activation and every disjunct whose indicator is one has its rows in their
scalar sets. The set carries the scalar set of every row, so it describes the
whole disjunction on its own.

Rather than recomputing offsets, a solver locates the pieces with
[`num_disjuncts`](@ref), [`activation_index`](@ref),
[`indicator_indices`](@ref), and [`row_indices`](@ref):

```julia
function handle(func, set::DisjunctionSet)
    activation = func[activation_index(set)]
    indicators = func[indicator_indices(set)]
    for i in 1:num_disjuncts(set)
        rows = func[row_indices(set, i)]
        sets = set.inner_sets[i]
        # build disjunct i from `rows .in sets`, governed by `indicators[i]`
    end
end
```

A top-level disjunction has the constant activation `1`. A nested disjunction is
lowered to its own constraint whose activation is the indicator expression of
the parent disjunct, so nesting never appears inside the set itself.
[`SupportedInnerSet`](@ref) is the union of scalar sets a row may carry, which a
solver can use to declare or check what it supports.

This is the whole interface between the two packages:
`DisjunctiveProgramming` owns the set and the lowering,
and the solver package,
[DisjunctiveAlgorithms.jl](https://github.com/infiniteopt/DisjunctiveAlgorithms.jl)
being the one written against it, owns the algorithms that consume it.

## Reformulation Tags

An extension that needs its own behaviour on the binary variables created during
reformulation can attach a tag to logical variables, which is forwarded to
`@variable` when each binary is built. See
[Reformulation Tags](@ref reformulation_tags) in the user guide for the syntax.
