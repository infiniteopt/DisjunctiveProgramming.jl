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

################################################################################
#                        DISJUNCTION SET RAISING
################################################################################
# Inverse of the lowering above, for models copied in from MOI: each
# `DisjunctionSet` becomes a disjunction whose logical variables reuse its bin

function _affine_part(vref::JuMP.AbstractVariableRef)
    T = JuMP.value_type(typeof(JuMP.owner_model(vref)))
    return convert(JuMP.GenericAffExpr{T, typeof(vref)}, vref)
end
_affine_part(expr::JuMP.GenericAffExpr) = expr
# A quadratic row makes every entry a `QuadExpr`; one without quadratic terms
# is still affine
function _affine_part(expr::JuMP.GenericQuadExpr)
    isempty(expr.terms) && return expr.aff
    return error("`DisjunctionSet` indicator `$expr` is not affine.")
end
# Any other expression is not affine
function _affine_part(expr)
    return error("`DisjunctionSet` indicator `$expr` is not affine.")
end

# Binary `y` of an indicator
function _indicator_binary(indicator)
    aff = _affine_part(indicator)
    # y -> (y, false), 1 - y -> (y, true)
    if length(aff.terms) == 1
        bvref, coef = only(aff.terms)
        constant = JuMP.constant(aff)
        isone(coef) && iszero(constant) && return bvref, false
        isone(-coef) && isone(constant) && return bvref, true
    end
    return error("`DisjunctionSet` indicator `$indicator` must be a binary " *
                 "variable `y` or its complement `1 - y`.")
end

# Logical variable for an indicator, created on first use and reusing `y`
# as its binary
function _indicator_logical_variable(model, indicator_map, indicator)
    key = _indicator_binary(indicator)
    haskey(indicator_map, key) && return indicator_map[key]
    bvref, is_complement = key
    if is_complement
        complement_lvref = _indicator_logical_variable(model, indicator_map,
            bvref)
        lvar = LogicalVariable(nothing, nothing, complement_lvref)
        lvref = _add_logical_variable(model, lvar,
            "not_" * JuMP.name(complement_lvref))
    else
        JuMP.is_binary(bvref) || error(
            "`DisjunctionSet` indicator `$bvref` must be binary.")
        lvar = LogicalVariable(nothing, nothing, nothing)
        lvref = _add_logical_variable(model, lvar, JuMP.name(bvref), bvref)
    end
    indicator_map[key] = lvref
    return lvref
end

# Replace each `DisjunctionSet` by a disjunction (permanently). Parents and
# children share indicators through `indicator_map`, so order does not matter.
function _raise_disjunction_sets(model::JuMP.AbstractModel)
    return
end
function _raise_disjunction_sets(model::JuMP.GenericModel)
    indicator_map = Dict{Tuple{Any, Bool}, LogicalVariableRef}()
    parent_lvrefs = LogicalVariableRef[]
    for (F, S) in JuMP.list_of_constraint_types(model)
        S == DisjunctionSet || continue
        for cref in JuMP.all_constraints(model, F, S)
            con = JuMP.constraint_object(cref)
            func, set = con.func, con.set
            activation = _affine_part(func[activation_index(set)])
            is_nested = !(isempty(activation.terms) &&
                isone(activation.constant))
            if is_nested
                parent_lvref = _indicator_logical_variable(
                    model, indicator_map, activation
                    )
                push!(parent_lvrefs, parent_lvref)
            end
            indicators = [_indicator_logical_variable(model, indicator_map,
                indicator) for indicator in func[indicator_indices(set)]]
            for (disjunct_index, lvref) in enumerate(indicators)
                disjunct_rows = func[row_indices(set, disjunct_index)]
                for (row_func, row_set) in
                    zip(disjunct_rows, set.inner_sets[disjunct_index])
                    # affine form: reformulations reject a bare variable here
                    if row_func isa JuMP.AbstractVariableRef
                        row_func = _affine_part(row_func)
                    end
                    JuMP.@constraint(model, row_func in row_set, Disjunct(lvref))
                end
            end
            name = JuMP.name(cref)
            if is_nested
                disjunction(model, indicators, Disjunct(parent_lvref), name)
            else
                disjunction(model, indicators, name)
            end
            JuMP.delete(model, cref)
        end
    end
    # a nested disjunction under a non-disjunct indicator would be dropped
    disjunct_indicators = Set(lvref
        for disjunction_data in values(_disjunctions(model))
        for lvref in disjunction_data.constraint.indicators)
    for parent_lvref in parent_lvrefs
        parent_lvref in disjunct_indicators || error(
            "`DisjunctionSet` activation `$parent_lvref` is not the " *
            "indicator of any disjunct.")
    end
    return
end
