```@meta
DocTestFilters = [r"≤|<=", r"≥|>=", r" == | = ", r" ∈ | in ",
                  r"MathOptInterface|MOI"]
```

# [Logical Variables](@id variables_guide)

A guide for logical variables in `DisjunctiveProgramming`. See the respective
[technical manual](@ref variables_manual) for more details.

## Overview

A logical variable is a Boolean decision. It takes the value `true` or `false`,
and its job in a GDP model is to indicate whether the constraints of a
particular disjunct are enforced. Logical variables are distinct from JuMP's
binary variables: they cannot appear inside algebraic constraints, and they are
not handed to the solver as they stand. During reformulation each one is
replaced by a binary variable, and the constraints tagged to it are encoded in
terms of that binary.

Keeping the two kinds of variable separate is what lets us reformulate a single
model in several different ways. The logical layer records the decision
structure, and the reformulation decides how that structure becomes algebra.

## Basic Usage

We declare logical variables with `@variable` using the [`Logical`](@ref)
variable type. They support the same container syntax as any JuMP variable:

```jldoctest gdp_vars; setup = :(using DisjunctiveProgramming, HiGHS)
julia> model = GDPModel();

julia> @variable(model, Y, Logical);

julia> @variable(model, Z[1:3], Logical);

julia> @variable(model, W[1:2, 1:3], Logical);
```

We can supply a start value at declaration:

```jldoctest gdp_vars
julia> @variable(model, V[1:2], Logical, start = true);
```

!!! warning
    There is no `fix` keyword on the `@variable` declaration. To hold a logical
    variable at a value, declare it and then call `fix` on it, as shown under
    [Modification](@ref var_modification) below.

### Logical Complements

When a decision is genuinely binary, we can declare the second alternative as
the complement of the first. The complement is not an independent variable: its
value is constrained to be the negation of the variable it complements, so we
need no separate exclusivity constraint.

```jldoctest gdp_vars
julia> @variable(model, use_process, Logical);

julia> @variable(model, skip_process, Logical, logical_complement = use_process);

julia> has_logical_complement(skip_process)
true
```

Using a complement rather than two free logical variables reduces the number of
binaries in the reformulated program, so it is worth doing whenever a
disjunction has exactly two disjuncts.

### Logical Variables Over a Continuous Domain

In a model built with `InfiniteOpt`, a logical variable can be declared over an
infinite parameter with [`InfiniteLogical`](@ref), which decides it at every
support rather than once. See [Infinite GDP Models](@ref infinite_guide).

## Queries

We can query the Boolean state of a variable and its relationship to the
reformulated model:

```jldoctest gdp_vars
julia> start_value(V[1])
true

julia> is_fixed(Y)
false
```

The binary variable that stands in for a logical variable after reformulation is
reached with [`binary_variable`](@ref):

```jldoctest gdp_vars
julia> binary_variable(Y)
Y
```

After a solve, `value` gives us a `Bool`. Let's build a small model and check:

```jldoctest gdp_vars
julia> solved = GDPModel(HiGHS.Optimizer);

julia> set_silent(solved)

julia> @variable(solved, 0 <= x <= 10);

julia> @variable(solved, S[1:2], Logical);

julia> @constraint(solved, x <= 3, Disjunct(S[1]));

julia> @constraint(solved, x >= 7, Disjunct(S[2]));

julia> @disjunction(solved, S);

julia> @objective(solved, Max, x);

julia> optimize!(solved)

julia> value.(S)
2-element BitVector:
 0
 1
```

## [Modification](@id var_modification)

Logical variables support the usual JuMP modification methods. We use `fix` to
hold a variable at a Boolean value, which is how we force a disjunct in or out
of the solution:

```jldoctest gdp_vars
julia> fix(Y, true)

julia> is_fixed(Y), fix_value(Y)
(true, true)

julia> unfix(Y)

julia> is_fixed(Y)
false
```

We can also set start values and names after declaration:

```jldoctest gdp_vars
julia> set_start_value(Y, false)

julia> set_name(Y, "use_first_process")

julia> name(Y)
"use_first_process"
```

!!! tip
    Fixing a logical variable is the right way to assert that a single decision
    is true or false. Writing a logical constraint on a lone variable, such as
    `@constraint(model, Y := true)`, is rejected precisely because `fix` already
    expresses it, and does so without adding a constraint to the reformulated
    program.

## [Reformulation Tags](@id reformulation_tags)

We can give the binary variable created for a logical variable a tag, which is
forwarded to `@variable` as the variable type when the binary is built. This is
an extension mechanism: it lets another package attach its own variable
behaviour to the binaries that reformulation produces.

A tag is any type for which `JuMP.build_variable` is defined:

```jldoctest gdp_vars
julia> struct MyTag end

julia> function JuMP.build_variable(::Function, info::JuMP.VariableInfo, ::MyTag; kwargs...)
           return JuMP.ScalarVariable(info)
       end

julia> tagged = GDPModel();

julia> @variable(tagged, T[1:2], Logical(MyTag()));
```

Every binary variable created for `T` during reformulation is then built through
the `MyTag` method rather than the default one.
