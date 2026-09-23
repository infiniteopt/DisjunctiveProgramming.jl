module InfiniteDisjunctiveProgramming

import JuMP.MOI as _MOI
import InfiniteOpt, JuMP
import DisjunctiveProgramming as DP

################################################################################
#                                   MODEL
################################################################################
function DP.InfiniteGDPModel(args...; kwargs...)
    return DP.GDPModel{
        InfiniteOpt.InfiniteModel,
        InfiniteOpt.GeneralVariableRef,
        InfiniteOpt.InfOptConstraintRef
        }(args...; kwargs...)
end

function DP.collect_all_vars(model::InfiniteOpt.InfiniteModel)
    vars = JuMP.all_variables(model)
    derivs = InfiniteOpt.all_derivatives(model)
    return append!(vars, derivs)
end

################################################################################
#                                 VARIABLES
################################################################################
DP.InfiniteLogical(prefs...) = DP.Logical(InfiniteOpt.Infinite(prefs...))

_is_parameter(vref::InfiniteOpt.GeneralVariableRef) =
    _is_parameter(InfiniteOpt.dispatch_variable_ref(vref))
_is_parameter(::InfiniteOpt.DependentParameterRef) = true
_is_parameter(::InfiniteOpt.IndependentParameterRef) = true
_is_parameter(::InfiniteOpt.ParameterFunctionRef) = true
_is_parameter(::InfiniteOpt.FiniteParameterRef) = true
_is_parameter(::Any) = false

function DP.requires_disaggregation(vref::InfiniteOpt.GeneralVariableRef)
    return !_is_parameter(vref)
end

function DP.VariableProperties(vref::InfiniteOpt.GeneralVariableRef)
    info = DP.get_variable_info(vref)
    name = JuMP.name(vref)
    set = nothing
    prefs = InfiniteOpt.parameter_refs(vref)
    var_type = !isempty(prefs) ? InfiniteOpt.Infinite(prefs...) : nothing
    return DP.VariableProperties(info, name, set, var_type)
end

# Extract parameter refs from expression and return VariableProperties with Infinite type
function DP.VariableProperties(
    expr::Union{
        JuMP.GenericAffExpr{C, InfiniteOpt.GeneralVariableRef},
        JuMP.GenericQuadExpr{C, InfiniteOpt.GeneralVariableRef},
        JuMP.GenericNonlinearExpr{InfiniteOpt.GeneralVariableRef}
    }
) where C
    prefs = InfiniteOpt.parameter_refs(expr)
    info = DP._free_variable_info()
    var_type = !isempty(prefs) ? InfiniteOpt.Infinite(prefs...) : nothing
    return DP.VariableProperties(info, "", nothing, var_type)
end

function DP.VariableProperties(
    exprs::Vector{<:Union{
        InfiniteOpt.GeneralVariableRef,
        JuMP.GenericAffExpr{<:Any, InfiniteOpt.GeneralVariableRef},
        JuMP.GenericQuadExpr{<:Any, InfiniteOpt.GeneralVariableRef},
        JuMP.GenericNonlinearExpr{InfiniteOpt.GeneralVariableRef}
    }}
)
    all_prefs = Set{InfiniteOpt.GeneralVariableRef}()
    for expr in exprs
        for pref in InfiniteOpt.parameter_refs(expr)
            push!(all_prefs, pref)
        end
    end
    prefs = Tuple(all_prefs)
    info = DP._free_variable_info()
    var_type = !isempty(prefs) ? InfiniteOpt.Infinite(prefs...) : nothing
    return DP.VariableProperties(info, "", nothing, var_type)
end

function JuMP.value(vref::DP.LogicalVariableRef{InfiniteOpt.InfiniteModel})
    return JuMP.value(DP.binary_variable(vref)) .>= 0.5
end

################################################################################
#                                CONSTRAINTS
################################################################################
function JuMP.add_constraint(
    model::InfiniteOpt.InfiniteModel,
    c::JuMP.VectorConstraint{F, S},
    name::String = ""
) where {F, S <: DP.AbstractCardinalitySet}
    return DP._add_cardinality_constraint(model, c, name)
end

function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{DP._LogicalExpr{M}, S},
    name::String = ""
) where {S, M <: InfiniteOpt.InfiniteModel}
    return DP._add_logical_constraint(model, c, name)
end

function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{DP.LogicalVariableRef{M}, S},
    name::String = ""
) where {M <: InfiniteOpt.InfiniteModel, S}
    error("Cannot define constraint on single logical variable, use `fix` instead.")
end

function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{
        JuMP.GenericAffExpr{C, DP.LogicalVariableRef{M}}, S
    },
    name::String = ""
) where {M <: InfiniteOpt.InfiniteModel, S, C}
    error("Cannot add, subtract, or multiply with logical variables.")
end

function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{
        JuMP.GenericQuadExpr{C, DP.LogicalVariableRef{M}}, S
    },
    name::String = ""
) where {M <: InfiniteOpt.InfiniteModel, S, C}
    error("Cannot add, subtract, or multiply with logical variables.")
end

################################################################################
#                                  METHODS
################################################################################
function DP.get_constant(
    expr::JuMP.GenericAffExpr{T, InfiniteOpt.GeneralVariableRef}
) where {T}
    constant = JuMP.constant(expr)
    param_expr = zero(typeof(expr))
    for (var, coeff) in expr.terms
        if _is_parameter(var)
            JuMP.add_to_expression!(param_expr, coeff, var)
        end
    end
    return constant + param_expr
end

function DP.disaggregate_expression(
    model::M,
    aff::JuMP.GenericAffExpr,
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::DP._Hull
) where {M <: InfiniteOpt.InfiniteModel}
    terms = Any[aff.constant * bvref]
    for (vref, coeff) in aff.terms
        if JuMP.is_binary(vref)
            push!(terms, coeff * vref)
        elseif vref isa InfiniteOpt.GeneralVariableRef && _is_parameter(vref)
            push!(terms, coeff * vref * bvref)
        elseif !haskey(method.disjunct_variables, (vref, bvref))
            push!(terms, coeff * vref)
        else
            dvref = method.disjunct_variables[vref, bvref]
            push!(terms, coeff * dvref)
        end
    end
    return JuMP.@expression(model, sum(terms))
end

################################################################################
#                          MBM FOR INFINITEMODEL
################################################################################

# Copy the InfiniteModel, strip everything but VariableInfo bounds,
# add back the selected disjunct constraints, transcribe, and return
# only the other disjunct's constraints plus variable bounds.
function DP.copy_model_with_constraints(
    model::InfiniteOpt.InfiniteModel,
    constraints::Vector{<:DP.DisjunctConstraintRef},
    method::DP._MBM
    )
    # Filter out every source constraint at copy time instead of
    # copying then deleting. Equivalent end state, fewer allocations.
    mini, ref_map = JuMP.copy_model(
        model; filter_constraints = cref -> false
        )

    for cref in constraints
        con = JuMP.constraint_object(cref)
        T = one(JuMP.value_type(typeof(mini)))
        JuMP.@constraint(mini, ref_map[con.func] * T in con.set)
    end

    InfiniteOpt.build_transformation_backend!(mini)
    transcribed = InfiniteOpt.transformation_model(mini)
    JuMP.set_optimizer(transcribed, method.optimizer)
    JuMP.set_silent(transcribed)

    # fwd_map needs every ref reachable from disjunct constraints —
    # decision vars + parameters + parameter functions so the
    # objective substitution in `prepare_max_M_objective` can look up
    # any term it sees.
    decision_vars = DP.collect_all_vars(model)
    fwd_map = Dict{InfiniteOpt.GeneralVariableRef,
        Vector{InfiniteOpt.GeneralVariableRef}}()
    for v in decision_vars
        fwd_map[v] = [ref_map[v]]
    end
    for p in InfiniteOpt.all_parameters(model)
        fwd_map[p] = [ref_map[p]]
    end
    for pf in InfiniteOpt.all_parameter_functions(model)
        fwd_map[pf] = [ref_map[pf]]
    end
    return DP.GDPSubmodel(mini, decision_vars, fwd_map)
end

function DP.prepare_max_M_objective(
    ::InfiniteOpt.InfiniteModel,
    obj::JuMP.ScalarConstraint{T, S},
    sub::DP.GDPSubmodel
    ) where {T, S <: _MOI.LessThan}
    flat_map = Dict(v => ws[1] for (v, ws) in sub.fwd_map)
    obj_func = DP.replace_variables_in_constraint(obj.func, flat_map)
    return obj_func - obj.set.upper
end

function DP.prepare_max_M_objective(
    ::InfiniteOpt.InfiniteModel,
    obj::JuMP.ScalarConstraint{T, S},
    sub::DP.GDPSubmodel
    ) where {T, S <: _MOI.GreaterThan}
    flat_map = Dict(v => ws[1] for (v, ws) in sub.fwd_map)
    obj_func = DP.replace_variables_in_constraint(obj.func, flat_map)
    return obj.set.lower - obj_func
end

# Candidate indices along one axis of the M array: the corners of the
# grid cell bracketing a scalar query (independent parameter), or the
# column matching a joint-support query (dependent group; every column
# when the query is off-support, so the estimate stays conservative)
function _axis_candidates(grid::AbstractVector{<:Real}, arg::Real)
    lo = clamp(searchsortedlast(grid, arg), 1, length(grid) - 1)
    return lo:(lo + 1)
end
function _axis_candidates(grid::AbstractMatrix{<:Real}, arg)
    j = findfirst(k -> isapprox(view(grid, :, k), arg, atol = 1e-10),
                  axes(grid, 2))
    return isnothing(j) ? axes(grid, 2) : (j:j)
end

# Constant interpolation: max of `values` over the candidate indices
function _interpolate(grids::Tuple, values::AbstractArray{<:Real})
    # mimic the call form of Interpolations.jl's interpolation
    return (args...) -> maximum(
        values[I...] for I in Iterators.product(
            map(_axis_candidates, grids, args)...))
end

# The infinite parameters of `mini_expr` and their supports, in the
# ascending order of `parameter_refs`. An independent parameter gives
# its sorted support vector; a dependent group gives the matrix whose
# columns are its joint supports. Grids are read off the mini model so
# their column order matches the transcription axes; the returned
# prefs are the main-model parameters.
function _support_grids(
    sub::DP.GDPSubmodel, mini_expr::JuMP.AbstractJuMPScalar)
    reverse_map = Dict(ws[1] => v for (v, ws) in sub.fwd_map)
    mini_prefs = InfiniteOpt.parameter_refs(mini_expr)
    prefs = Tuple(getindex.(Ref(reverse_map), p) for p in mini_prefs)
    return prefs, Tuple(InfiniteOpt.supports(p) for p in mini_prefs)
end

# Solve the M subproblem exactly at every support
function DP.sample_M_values(
    sampler::DP.ExhaustiveSampler,
    objectives::AbstractArray,
    sub::DP.GDPSubmodel,
    method::DP._MBM,
    support_grids::Tuple
    )
    M_vals = Array{Float64}(undef, size(objectives))
    for I in eachindex(objectives)
        m = DP.raw_M(sub, objectives[I], method)
        m === nothing && return nothing
        M_vals[I] = m
    end
    return M_vals
end

# Transcribe mini_expr, compute the per-support M values with the
# method's sampler, and aggregate to a scalar if uniform, else to a
# parameter function on main. A finite mini_expr transcribes to one
# expression, so its single M subproblem is solved directly.
function DP.raw_M(
    sub::DP.GDPSubmodel{<:InfiniteOpt.InfiniteModel},
    mini_expr::JuMP.AbstractJuMPScalar,
    method::DP._MBM
    )
    objectives = InfiniteOpt.transformation_expression(mini_expr)
    transcribed = InfiniteOpt.transformation_model(sub.model)
    inner_sub = DP.GDPSubmodel(transcribed, JuMP.VariableRef[],
        Dict{JuMP.VariableRef, Vector{JuMP.VariableRef}}())
    if objectives isa JuMP.AbstractJuMPScalar
        return DP.raw_M(inner_sub, objectives, method)
    end
    # transcription orders the dimensions by parameter group, which is
    # not the ascending order `parameter_refs` gives the grids below
    group_idxs = InfiniteOpt.parameter_group_int_indices(mini_expr)
    if length(group_idxs) > 1 && ndims(objectives) == length(group_idxs)
        objectives = permutedims(objectives, sortperm(group_idxs))
    end
    prefs, grids = _support_grids(sub, mini_expr)
    M_vals = DP.sample_M_values(method.sampler, objectives,
        inner_sub, method, grids)
    M_vals === nothing && return nothing
    M_vals isa Number && return M_vals
    all(==(first(M_vals)), M_vals) && return first(M_vals)
    main = JuMP.owner_model(first(keys(sub.fwd_map)))
    param_func = InfiniteOpt.build_parameter_function(
        error, _interpolate(grids, M_vals), prefs)
    return InfiniteOpt.add_parameter_function(main, param_func)
end

################################################################################
#                    CUTTING PLANES FOR INFINITEMODEL
################################################################################

# Build CP subproblem: reformulate the InfiniteModel in-place, transcribe,
# copy, and wrap in GDPSubmodel with forward variable map.
function DP.copy_and_reformulate(
    model::InfiniteOpt.InfiniteModel,
    decision_vars::Vector{InfiniteOpt.GeneralVariableRef},
    reform_method::DP.AbstractReformulationMethod,
    method::DP._CuttingPlanes
    )
    DP.reformulate_model(model, reform_method)
    InfiniteOpt.build_transformation_backend!(model)
    for (v, w) in _compute_quadrature_weights(model, decision_vars)
        method.weights[v] = w
    end
    transcribed = InfiniteOpt.transformation_model(model)
    sub_copy, copy_map = JuMP.copy_model(transcribed)
    fwd_map = Dict{InfiniteOpt.GeneralVariableRef, Vector{JuMP.VariableRef}}()
    for v in decision_vars
        transcription_var = InfiniteOpt.transformation_variable(v)
        tvars = isempty(InfiniteOpt.parameter_refs(v)) ?
            [transcription_var] : vec(transcription_var)
        fwd_map[v] = [copy_map[tv] for tv in tvars]
    end
    sub = DP.GDPSubmodel(sub_copy, decision_vars, fwd_map)
    JuMP.set_optimizer(sub.model, method.optimizer)
    JuMP.set_silent(sub.model)
    return sub
end

# One infinite parameter group: a scalar parameter, or the refs of a
# dependent group. Both `parameter_refs(vref)` entries and
# `parameter_refs(data)` take these two shapes.
const _ParameterGroup = Union{InfiniteOpt.GeneralVariableRef,
    Vector{InfiniteOpt.GeneralVariableRef}}

# One support of a group: a value, or a joint support.
const _GroupSupport = Union{Float64, Vector{Float64}}

const _MeasureDataMap = Dict{_ParameterGroup,
    InfiniteOpt.AbstractMeasureData}

# Collect the objective's measure data (nested measures included),
# keyed by the group the measure acts on, so a measure spanning
# several parameters only matches a variable depending on that same
# group. A group measured twice keeps the last measure found.
_collect_measure_data(data, expr::Number) = nothing
function _collect_measure_data(data::Dict, expr::InfiniteOpt.GeneralVariableRef)
    dispatch = InfiniteOpt.dispatch_variable_ref(expr)
    dispatch isa InfiniteOpt.MeasureRef || return nothing
    md = InfiniteOpt.measure_data(expr)
    data[InfiniteOpt.parameter_refs(md)] = md
    return _collect_measure_data(data, InfiniteOpt.measure_function(expr))
end
function _collect_measure_data(data::Dict, expr::JuMP.GenericAffExpr)
    for (v, _) in expr.terms
        _collect_measure_data(data, v)
    end
    return nothing
end
function _collect_measure_data(data::Dict, expr::JuMP.GenericQuadExpr)
    _collect_measure_data(data, expr.aff)
    for (pair, _) in expr.terms
        _collect_measure_data(data, pair.a)
        _collect_measure_data(data, pair.b)
    end
    return nothing
end
function _collect_measure_data(data::Dict, expr::JuMP.GenericNonlinearExpr)
    for arg in expr.args
        _collect_measure_data(data, arg)
    end
    return nothing
end

# The parameter a group rounds its supports by.
_group_parameter(group::InfiniteOpt.GeneralVariableRef) = group
_group_parameter(group::Vector{InfiniteOpt.GeneralVariableRef}) = first(group)

# Whether a (scalar) parameter ranges over a plain interval;
# dependent groups and distribution parameters return false.
_is_interval_parameter(::Vector{InfiniteOpt.GeneralVariableRef}) = false
function _is_interval_parameter(pref::InfiniteOpt.GeneralVariableRef)
    dispatch = InfiniteOpt.dispatch_variable_ref(pref)
    return InfiniteOpt.infinite_domain(dispatch) isa
        InfiniteOpt.IntervalDomain
end

const _ScalarMeasureData = Union{
    InfiniteOpt.DiscreteMeasureData{InfiniteOpt.GeneralVariableRef, 1},
    InfiniteOpt.FunctionalDiscreteMeasureData{InfiniteOpt.GeneralVariableRef}
    }
const _MultiMeasureData = Union{
    InfiniteOpt.DiscreteMeasureData{Vector{InfiniteOpt.GeneralVariableRef}, 2},
    InfiniteOpt.FunctionalDiscreteMeasureData{
        Vector{InfiniteOpt.GeneralVariableRef}}
    }

# Weights one parameter group, keyed the way the transcription grid
# stores its supports. Discrete data holds raw support values but the
# parameter rounds them on insertion, so the keys are rounded to match.
function _group_weights(
    data::_ScalarMeasureData,
    group::_ParameterGroup,
    group_supports::Vector{<:_GroupSupport}
    )
    sig_digits = InfiniteOpt.significant_digits(_group_parameter(group))
    supps = InfiniteOpt.supports(data)
    weight_func = InfiniteOpt.weight_function(data)
    return Dict{Float64, Float64}(
        round(supps[i], sigdigits = sig_digits) => coeff * weight_func(supps[i])
        for (i, coeff) in enumerate(InfiniteOpt.coefficients(data)))
end
function _group_weights(
    data::_MultiMeasureData,
    group::_ParameterGroup,
    group_supports::Vector{<:_GroupSupport}
    )
    sig_digits = InfiniteOpt.significant_digits(_group_parameter(group))
    supps = InfiniteOpt.supports(data)
    weight_func = InfiniteOpt.weight_function(data)
    return Dict{Vector{Float64}, Float64}(
        round.(supps[:, i], sigdigits = sig_digits) =>
            coeff * weight_func(supps[:, i])
        for (i, coeff) in enumerate(InfiniteOpt.coefficients(data)))
end

# The objective never measures the group: a default integral for a
# scalar interval parameter, a uniform average otherwise.
function _group_weights(
    ::Nothing,
    group::_ParameterGroup,
    group_supports::Vector{<:_GroupSupport}
    )
    if _is_interval_parameter(group)
        data = InfiniteOpt.generate_integral_data(group,
            JuMP.lower_bound(group), JuMP.upper_bound(group),
            InfiniteOpt.UniTrapezoid())
        return _group_weights(data, group, group_supports)
    end
    values = unique(group_supports)
    return Dict(value => 1 / length(values) for value in values)
end

# Measure data that reports no weights of its own takes the default.
function _group_weights(
    data::InfiniteOpt.AbstractMeasureData,
    group::_ParameterGroup,
    group_supports::Vector{<:_GroupSupport}
    )
    @warn "Cannot read quadrature weights from measure data of type " *
        "`$(typeof(data))`; using the default weighting instead." maxlog = 1
    return _group_weights(nothing, group, group_supports)
end

# Quadrature weights read off the objective's measure data
function _compute_quadrature_weights(
    model::InfiniteOpt.InfiniteModel,
    decision_vars::Vector{InfiniteOpt.GeneralVariableRef}
    )
    measure_data = _MeasureDataMap()
    _collect_measure_data(measure_data, JuMP.objective_function(model))
    weights = Dict{InfiniteOpt.GeneralVariableRef, Vector{Float64}}()
    for v in decision_vars
        prefs = InfiniteOpt.parameter_refs(v)
        if isempty(prefs)
            weights[v] = [1.0]
            continue
        end
        supps = vec(InfiniteOpt.supports(v))
        group_weights = [
            _group_weights(get(measure_data, group, nothing), group,
                [supp[j] for supp in supps])
            for (j, group) in enumerate(prefs)]
        weights[v] = [prod(get(group_weights[j], supp[j], 0.0)
            for j in eachindex(group_weights)) for supp in supps]
    end
    return weights
end

# Read per-support values from the transformation backend.
function DP.extract_solution(
    model::InfiniteOpt.InfiniteModel,
    reform_state::DP._CuttingPlanes
    )
    sol = Dict{InfiniteOpt.GeneralVariableRef, Vector{Float64}}()
    for v in reform_state.decision_vars
        transcription_var = InfiniteOpt.transformation_variable(v)
        var_prefs = InfiniteOpt.parameter_refs(v)
        sol[v] = isempty(var_prefs) ? [JuMP.value(transcription_var)] :
            JuMP.value.(vec(transcription_var))
    end
    return sol
end

# Add a quadrature-weighted cut directly to the transformation backend
# and mark it ready so the next optimize! doesn't re-transcribe and
# wipe the cut.
function DP.add_cut(
    model::InfiniteOpt.InfiniteModel,
    reform_state::DP._CuttingPlanes,
    rBM_sol::Dict{<:JuMP.AbstractVariableRef, <:Vector{<:Number}},
    sep_sol::Dict{<:JuMP.AbstractVariableRef, <:Vector{<:Number}}
    )
    transcribed = InfiniteOpt.transformation_model(model)
    cut_expr = zero(JuMP.AffExpr)
    for var in reform_state.decision_vars
        rbm_vals = rBM_sol[var]
        sep_vals = sep_sol[var]
        transcription_var = InfiniteOpt.transformation_variable(var)
        transcribed_vars = transcription_var isa AbstractArray ?
            vec(transcription_var) : [transcription_var]
        w = reform_state.weights[var]
        for k in eachindex(transcribed_vars)
            xi = 2 * w[k] * (sep_vals[k] - rbm_vals[k])
            JuMP.add_to_expression!(cut_expr, xi, transcribed_vars[k])
            JuMP.add_to_expression!(cut_expr, -xi * sep_vals[k])
        end
    end
    JuMP.@constraint(transcribed, cut_expr >= 0)
    InfiniteOpt.set_transformation_backend_ready(model, true)
    return
end

end
