################################################################################
#                        DISJUNCTION SET LOWERING
################################################################################
"""
    Direct()

Reformulation method that passes the disjunctions to the solver
directly: each disjunction is lowered to a single vector constraint
in [`DisjunctionSet`](@ref), so the model can be solved by an MOI
optimizer that supports the set, such as
`DisjunctiveAlgorithms.Optimizer`.

**Example**
```julia
julia> using DisjunctiveProgramming, DisjunctiveAlgorithms, HiGHS, Ipopt

julia> model = GDPModel(() -> DisjunctiveAlgorithms.Optimizer(
           Ipopt.Optimizer, HiGHS.Optimizer));

julia> optimize!(model, gdp_method = Direct())
```
"""
struct Direct <: AbstractReformulationMethod end

requires_exactly1(::Direct) = true

# One flat constraint per disjunction: [activation, indicators,
# rows]. Nested disjunctions get their own constraint with the parent
# indicator as the activation. InfiniteOpt transcribes per support.
function reformulate_disjunction(
    model::JuMP.AbstractModel,
    disj::Disjunction,
    method::Direct
    )
    constraints = JuMP.AbstractConstraint[]
    _lower_disjunction(constraints, model, disj, 1.0)
    return constraints
end

function _lower_disjunction(
    constraints::Vector{JuMP.AbstractConstraint},
    model::JuMP.AbstractModel,
    disj::Disjunction,
    activation
    )
    indicators = JuMP.AbstractJuMPScalar[]
    rows = JuMP.AbstractJuMPScalar[]
    inner_sets = Vector{_MOI.AbstractScalarSet}[]
    for lvref in disj.indicators
        indicator = 1.0 * binary_variable(lvref)
        push!(indicators, indicator)
        sets = _MOI.AbstractScalarSet[]
        for cref in get(_indicator_to_constraints(model), lvref, [])
            constraint = JuMP.constraint_object(cref)
            if constraint isa Disjunction
                haskey(_exactly1_constraints(model), cref) || error(
                    "`Direct` requires nested " *
                    "disjunctions created with `exactly1 = true`.")
                _lower_disjunction(constraints, model, constraint,
                    indicator)
            else
                push!(rows, constraint.func)
                push!(sets, constraint.set)
            end
        end
        push!(inner_sets, sets)
    end
    push!(constraints, JuMP.VectorConstraint(
        collect(promote(1.0 * activation, indicators..., rows...)),
        DisjunctionSet(inner_sets)))
    return
end

# transcription may collapse the constant activation to a number;
# promote back to a uniform expression vector
function JuMP.build_constraint(
    ::Function,
    func::AbstractVector{<:JuMP.AbstractJuMPScalar},
    set::DisjunctionSet
    )
    return JuMP.VectorConstraint(func, set)
end

function JuMP.build_constraint(
    ::Function,
    func::AbstractVector{<:Union{Number, JuMP.AbstractJuMPScalar}},
    set::DisjunctionSet
    )
    return JuMP.VectorConstraint(collect(promote(func...)), set)
end

function JuMP.build_constraint(
    ::Function,
    func::AbstractVector,
    set::DisjunctionSet
    )
    return JuMP.VectorConstraint(collect(promote(func...)), set)
end
