module InfiniteDisjunctiveProgramming

import JuMP.MOI as _MOI
import InfiniteOpt, JuMP, Interpolations
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
# Reuses the finite MBM infrastructure by overriding:
# copy_model_with_constraints (build mini InfiniteModel, transcribe to
# flat JuMP, stash mini + main->mini ref_map in sub.model.ext),
# prepare_max_M_objective (translate main-model slack expr to mini-level
# then call InfiniteOpt.transformation_expression to get K flat
# objectives), and raw_M (vector dispatch aggregates K per-support M
# values into a parameter function).

# Collect all parameter function refs from all disjunct constraints in
# the model.
function _all_param_functions(model::InfiniteOpt.InfiniteModel)
    param_funcs = Set{InfiniteOpt.GeneralVariableRef}()
    for (_, crefs) in DP._indicator_to_constraints(model)
        for cref in crefs
            cref isa DP.DisjunctConstraintRef || continue
            con = JuMP.constraint_object(cref)
            for v in InfiniteOpt.all_expression_variables(con.func)
                dispatch_var = InfiniteOpt.dispatch_variable_ref(v)
                if dispatch_var isa InfiniteOpt.ParameterFunctionRef
                    push!(param_funcs, v)
                end
            end
        end
    end
    return param_funcs
end

# Build mini InfiniteModel with only the given disjunct constraints,
# transcribe to flat JuMP model, return GDPSubmodel with forward map.
function DP.copy_model_with_constraints(
    model::InfiniteOpt.InfiniteModel,
    constraints::Vector{<:DP.DisjunctConstraintRef},
    method::DP._MBM
    )
    mini = InfiniteOpt.InfiniteModel()
    ref_map = Dict{InfiniteOpt.GeneralVariableRef,
        InfiniteOpt.GeneralVariableRef}()

    # 1. Copy infinite parameters with their supports
    for p in InfiniteOpt.all_parameters(model)
        domain = InfiniteOpt.infinite_domain(p)
        supports = Float64.(InfiniteOpt.supports(p))
        param = InfiniteOpt.build_parameter(error, domain; supports = supports)
        new_param = InfiniteOpt.add_parameter(mini, param, JuMP.name(p))
        ref_map[p] = new_param
    end

    # 2. Copy decision variables with bounds
    for v in JuMP.all_variables(model)
        _is_parameter(v) && continue
        prefs = InfiniteOpt.parameter_refs(v)
        var_type = isempty(prefs) ? nothing :
            InfiniteOpt.Infinite(Tuple(ref_map[p] for p in prefs)...)
        props = DP.VariableProperties(
            DP.get_variable_info(v), "", nothing, var_type)
        ref_map[v] = DP.create_variable(mini, props)
    end

    # 3. Copy derivatives with their bounds
    for d in InfiniteOpt.all_derivatives(model)
        vref = InfiniteOpt.derivative_argument(d)
        pref = InfiniteOpt.operator_parameter(d)
        new_d = InfiniteOpt.deriv(ref_map[vref], ref_map[pref])
        info = DP.get_variable_info(d)
        info.has_lb && JuMP.set_lower_bound(new_d, info.lower_bound)
        info.has_ub && JuMP.set_upper_bound(new_d, info.upper_bound)
        ref_map[d] = new_d
    end

    # 4. Copy parameter functions from ALL disjuncts (needed for
    # constraint transcription)
    param_funcs = _all_param_functions(model)
    for pfunc in param_funcs
        func = InfiniteOpt.raw_function(pfunc)
        prefs = InfiniteOpt.parameter_refs(pfunc)
        mapped_prefs = Tuple(ref_map[p] for p in prefs)
        new_pfunc = _make_parameter_function(mini, func, mapped_prefs...)
        ref_map[pfunc] = new_pfunc
    end

    # 5. Add disjunct constraints using existing ref_map
    for cref in constraints
        cref isa DP.DisjunctConstraintRef || continue
        con = JuMP.constraint_object(cref)
        new_func = DP._replace_variables_in_constraint(con.func, ref_map)
        T = one(JuMP.value_type(typeof(mini)))
        JuMP.@constraint(mini, new_func * T in con.set)
    end

    # 6. Transcribe mini InfiniteModel to flat JuMP model
    InfiniteOpt.build_transformation_backend!(mini)
    flat = InfiniteOpt.transformation_model(mini)
    JuMP.set_optimizer(flat, method.optimizer)
    JuMP.set_silent(flat)
    # Stash main + ref_map so prepare_max_M_objective can translate
    # main-model expressions and let InfiniteOpt transcribe them via
    # mini's backend. Also stash main so raw_M can return a parameter
    # function on main (where it will be used in BigM constraints).
    flat.ext[:inf_mbm_main] = model
    flat.ext[:inf_mbm_ref_map] = ref_map
    # fwd_map / decision_vars are CP-shaped fields on GDPSubmodel that
    # the MBM path through our overrides does not consult; pass empty
    # containers of the right types.
    return DP.GDPSubmodel(flat, InfiniteOpt.GeneralVariableRef[],
        Dict{InfiniteOpt.GeneralVariableRef, Vector{JuMP.VariableRef}}())
end

# Translate the constraint slack to the mini InfiniteModel via ref_map,
# then use InfiniteOpt.transformation_expression to get one JuMP scalar
# (or plain Real, for pure-parameter slacks) per support point.
function DP.prepare_max_M_objective(
    ::InfiniteOpt.InfiniteModel,
    obj::JuMP.ScalarConstraint{T, S},
    sub::DP.GDPSubmodel
    ) where {T, S <: _MOI.LessThan}
    ref_map = sub.model.ext[:inf_mbm_ref_map]
    mini_expr = DP._replace_variables_in_constraint(obj.func, ref_map)
    return InfiniteOpt.transformation_expression(mini_expr - obj.set.upper)
end

function DP.prepare_max_M_objective(
    ::InfiniteOpt.InfiniteModel,
    obj::JuMP.ScalarConstraint{T, S},
    sub::DP.GDPSubmodel
    ) where {T, S <: _MOI.GreaterThan}
    ref_map = sub.model.ext[:inf_mbm_ref_map]
    mini_expr = DP._replace_variables_in_constraint(obj.func, ref_map)
    return InfiniteOpt.transformation_expression(obj.set.lower - mini_expr)
end

# Real dispatch: pure-parameter slacks collapse to a constant at that
# support. Mirrors the max(value, 0) semantics of the scalar base.
DP.raw_M(::DP.GDPSubmodel, obj::Real, method::DP._MBM) =
    max(obj, zero(method.default_M))

# Solve the submodel for a vector of objectives (one per support point).
# Clears start values before each solve (Gurobi refuses NaN warmstarts
# that can linger from a prior unbounded solve) and delegates each
# element to the scalar base `raw_M` above.
function DP.raw_M(
    sub::DP.GDPSubmodel,
    objectives::Vector{<:Union{Real, JuMP.AbstractJuMPScalar}},
    method::DP._MBM
    )
    M_vals = typeof(method.default_M)[]
    for obj_expr in objectives
        JuMP.set_start_value.(JuMP.all_variables(sub.model), nothing)
        m = DP.raw_M(sub, obj_expr, method)
        m === nothing && return nothing
        push!(M_vals, m)
    end
    model = sub.model.ext[:inf_mbm_main]
    # Condense per-support values: scalar if uniform, else pfunc.
    all(==(M_vals[1]), M_vals) && return M_vals[1]
    prefs, supports = _collect_parameters(model)
    grids = Tuple(supports[p] for p in prefs)
    shape = Tuple(length(supports[p]) for p in prefs)
    func = Interpolations.linear_interpolation(grids, reshape(M_vals, shape),
        extrapolation_bc = Interpolations.Line())
    return _make_parameter_function(model, func, prefs...)
end

################################################################################
#                          TRANSCRIPTION HELPERS
################################################################################

# Replacement for @parameter_function in the case of using an interpolation.
# Example (1D interpolation):
#   func = Interpolations.linear_interpolation(grids, vals)
#   pfunc = _make_parameter_function(model, func, t)  # returns a pfunc ref
function _make_parameter_function(
    model::InfiniteOpt.InfiniteModel, func,
    prefs::InfiniteOpt.GeneralVariableRef...
    )
    wrapped_func = func isa Function ? func : ((args...) -> func(args...))
    pref_arg = length(prefs) == 1 ? only(prefs) : prefs
    builder = InfiniteOpt.build_parameter_function(
        error, wrapped_func, pref_arg)
    return InfiniteOpt.add_parameter_function(model, builder)
end

# Collect all infinite parameters and their supports from the model.
function _collect_parameters(model::InfiniteOpt.InfiniteModel)
    params = collect(InfiniteOpt.all_parameters(model))
    if isempty(params)
        error("Model has no infinite parameters.")
    end
    prefs = InfiniteOpt.GeneralVariableRef[p for p in params]
    supports = Dict{InfiniteOpt.GeneralVariableRef, Vector{Float64}}(
        p => Float64.(InfiniteOpt.supports(p)) for p in prefs)
    return prefs, supports
end


################################################################################
#                    CUTTING PLANES FOR INFINITEMODEL
################################################################################

# Build CP subproblem: reformulate the InfiniteModel in-place, transcribe
# to a flat JuMP copy, and wrap in GDPSubmodel with forward variable map.
function DP.copy_and_reformulate(
    model::InfiniteOpt.InfiniteModel,
    decision_vars::Vector{InfiniteOpt.GeneralVariableRef},
    reform_method::DP.AbstractReformulationMethod,
    method::DP.CuttingPlanes
    )
    DP.reformulate_model(model, reform_method)
    InfiniteOpt.build_transformation_backend!(model)
    flat = InfiniteOpt.transformation_model(model)
    transcription_fwd = Dict{InfiniteOpt.GeneralVariableRef,
        Vector{JuMP.VariableRef}}()
    for v in DP.collect_all_vars(model)
        transcription_var = InfiniteOpt.transformation_variable(v)
        var_prefs = InfiniteOpt.parameter_refs(v)
        transcription_fwd[v] = isempty(var_prefs) ?
            [transcription_var] : vec(transcription_var)
    end
    sub_copy, copy_map = JuMP.copy_model(flat)
    fwd_map = Dict{InfiniteOpt.GeneralVariableRef, Vector{JuMP.VariableRef}}()
    for v in decision_vars
        haskey(transcription_fwd, v) || continue
        fwd_map[v] = [copy_map[flat_var] for flat_var in transcription_fwd[v]]
    end
    sub = DP.GDPSubmodel(sub_copy, decision_vars, fwd_map)
    JuMP.set_optimizer(sub.model, method.optimizer)
    JuMP.set_silent(sub.model)
    return sub
end

# Extract per-support-point solutions from the InfiniteOpt transformation
# backend after optimize!(model, ignore_optimize_hook=true).
function DP.extract_solution(model::InfiniteOpt.InfiniteModel)
    dvars = DP.collect_cutting_planes_vars(model)
    V = eltype(dvars)
    T = JuMP.value_type(typeof(model))
    sol = Dict{V, Vector{T}}()
    for v in dvars
        transcription_var = InfiniteOpt.transformation_variable(v)
        var_prefs = InfiniteOpt.parameter_refs(v)
        sol[v] = isempty(var_prefs) ? [JuMP.value(transcription_var)] :
            JuMP.value.(vec(transcription_var))
    end
    return sol
end

# Add a flat-sum cut directly to the transformation backend, matching
# the SEP's unweighted Euclidean norm (Trespalacios & Grossmann 2016
# Eq. 11 applied in the joint transcribed variable space). Then mark
# the backend as ready so the next optimize! reuses the cut-enhanced
# flat model without re-transcribing (which would wipe the cut).
function DP.add_cut(
    model::InfiniteOpt.InfiniteModel,
    decision_vars::Vector{InfiniteOpt.GeneralVariableRef},
    rBM_sol::Dict{<:JuMP.AbstractVariableRef, <:Vector{<:Number}},
    sep_sol::Dict{<:JuMP.AbstractVariableRef, <:Vector{<:Number}}
    )
    flat = InfiniteOpt.transformation_model(model)
    cut_expr = zero(JuMP.GenericAffExpr{
        JuMP.value_type(typeof(flat)),
        JuMP.variable_ref_type(flat)})
    for var in decision_vars
        haskey(rBM_sol, var) || continue
        haskey(sep_sol, var) || continue
        rbm_vals = rBM_sol[var]
        sep_vals = sep_sol[var]
        transcription_var = InfiniteOpt.transformation_variable(var)
        flat_vars = transcription_var isa AbstractArray ?
            vec(transcription_var) : [transcription_var]
        for k in eachindex(flat_vars)
            xi = 2 * (sep_vals[k] - rbm_vals[k])
            JuMP.add_to_expression!(cut_expr, xi, flat_vars[k])
            JuMP.add_to_expression!(cut_expr, -xi * sep_vals[k])
        end
    end
    JuMP.@constraint(flat, cut_expr >= 0)
    InfiniteOpt.set_transformation_backend_ready(model, true)
    return
end

end
