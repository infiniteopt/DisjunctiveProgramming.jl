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

# Build a mini InfiniteModel holding only the given disjunct constraints,
# transcribe it, and return as a GDPSubmodel.
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

    # 4. Copy parameter functions (needed by ref_map substitution)
    for pfunc in InfiniteOpt.all_parameter_functions(model)
        func = InfiniteOpt.raw_function(pfunc)
        prefs = InfiniteOpt.parameter_refs(pfunc)
        mapped_prefs = Tuple(ref_map[p] for p in prefs)
        pref_arg = length(mapped_prefs) == 1 ?
            only(mapped_prefs) : mapped_prefs
        param_func = InfiniteOpt.build_parameter_function(
            error, func, pref_arg)
        ref_map[pfunc] = InfiniteOpt.add_parameter_function(
            mini, param_func)
    end

    # 5. Add disjunct constraints using existing ref_map
    for cref in constraints
        cref isa DP.DisjunctConstraintRef || continue
        con = JuMP.constraint_object(cref)
        new_func = DP._replace_variables_in_constraint(con.func, ref_map)
        T = one(JuMP.value_type(typeof(mini)))
        JuMP.@constraint(mini, new_func * T in con.set)
    end

    # 6. Transcribe mini InfiniteModel
    InfiniteOpt.build_transformation_backend!(mini)
    transcribed = InfiniteOpt.transformation_model(mini)
    JuMP.set_optimizer(transcribed, method.optimizer)
    JuMP.set_silent(transcribed)
    # Stash for prepare_max_M_objective / raw_M.
    transcribed.ext[:inf_mbm_main] = model
    transcribed.ext[:inf_mbm_ref_map] = ref_map
    # GDPSubmodel's fwd_map / decision_vars are CP-only; unused here.
    return DP.GDPSubmodel(transcribed, InfiniteOpt.GeneralVariableRef[],
        Dict{InfiniteOpt.GeneralVariableRef, Vector{JuMP.VariableRef}}())
end

function DP.prepare_max_M_objective(
    ::InfiniteOpt.InfiniteModel,
    obj::JuMP.ScalarConstraint{T, S},
    sub::DP.GDPSubmodel
    ) where {T, S <: _MOI.LessThan}
    ref_map = sub.model.ext[:inf_mbm_ref_map]
    mini_expr = DP._replace_variables_in_constraint(
        obj.func, ref_map) - obj.set.upper
    sub.model.ext[:inf_mbm_obj_expr] = obj.func
    return InfiniteOpt.transformation_expression(mini_expr)
end

function DP.prepare_max_M_objective(
    ::InfiniteOpt.InfiniteModel,
    obj::JuMP.ScalarConstraint{T, S},
    sub::DP.GDPSubmodel
    ) where {T, S <: _MOI.GreaterThan}
    ref_map = sub.model.ext[:inf_mbm_ref_map]
    mini_expr = obj.set.lower - DP._replace_variables_in_constraint(
        obj.func, ref_map)
    sub.model.ext[:inf_mbm_obj_expr] = obj.func
    return InfiniteOpt.transformation_expression(mini_expr)
end

# Per-support solve, delegating to scalar base raw_M. Aggregated to a
# scalar if uniform, else to a parameter function.
function DP.raw_M(
    sub::DP.GDPSubmodel,
    objectives::AbstractArray{<:Union{JuMP.AbstractJuMPScalar, Real}},
    method::DP._MBM
    )
    M_vals = similar(objectives, typeof(method.default_M))
    for I in eachindex(objectives)
        JuMP.set_start_value.(JuMP.all_variables(sub.model), nothing)
        m = DP.raw_M(sub, objectives[I], method)
        m === nothing && return nothing
        M_vals[I] = m
    end
    all(==(first(M_vals)), M_vals) && return first(M_vals)
    main = sub.model.ext[:inf_mbm_main]
    expr = sub.model.ext[:inf_mbm_obj_expr]
    prefs = InfiniteOpt.parameter_refs(expr)
    grids = Tuple(InfiniteOpt.supports(p) for p in prefs)
    interp = Interpolations.linear_interpolation(grids, M_vals)
    param_func = InfiniteOpt.build_parameter_function(
        error, (args...) -> interp(args...), prefs)
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
    method::DP.CuttingPlanes
    )
    DP.reformulate_model(model, reform_method)
    InfiniteOpt.build_transformation_backend!(model)
    transcribed = InfiniteOpt.transformation_model(model)
    transcription_fwd = Dict{InfiniteOpt.GeneralVariableRef,
        Vector{JuMP.VariableRef}}()
    for v in DP.collect_all_vars(model)
        transcription_var = InfiniteOpt.transformation_variable(v)
        var_prefs = InfiniteOpt.parameter_refs(v)
        transcription_fwd[v] = isempty(var_prefs) ?
            [transcription_var] : vec(transcription_var)
    end
    sub_copy, copy_map = JuMP.copy_model(transcribed)
    fwd_map = Dict{InfiniteOpt.GeneralVariableRef, Vector{JuMP.VariableRef}}()
    for v in decision_vars
        haskey(transcription_fwd, v) || continue
        fwd_map[v] = [copy_map[transcribed_var] for transcribed_var in transcription_fwd[v]]
    end
    sub = DP.GDPSubmodel(sub_copy, decision_vars, fwd_map)
    JuMP.set_optimizer(sub.model, method.optimizer)
    JuMP.set_silent(sub.model)
    return sub
end

# Read per-support values from the transformation backend.
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

# Add a pointwise-sum cut directly to the transformation backend and mark
# it ready so the next optimize! doesn't re-transcribe and wipe the cut.
function DP.add_cut(
    model::InfiniteOpt.InfiniteModel,
    decision_vars::Vector{InfiniteOpt.GeneralVariableRef},
    rBM_sol::Dict{<:JuMP.AbstractVariableRef, <:Vector{<:Number}},
    sep_sol::Dict{<:JuMP.AbstractVariableRef, <:Vector{<:Number}}
    )
    transcribed = InfiniteOpt.transformation_model(model)
    cut_expr = zero(JuMP.GenericAffExpr{
        JuMP.value_type(typeof(transcribed)),
        JuMP.variable_ref_type(transcribed)})
    for var in decision_vars
        haskey(rBM_sol, var) || continue
        haskey(sep_sol, var) || continue
        rbm_vals = rBM_sol[var]
        sep_vals = sep_sol[var]
        transcription_var = InfiniteOpt.transformation_variable(var)
        transcribed_vars = transcription_var isa AbstractArray ?
            vec(transcription_var) : [transcription_var]
        for k in eachindex(transcribed_vars)
            xi = 2 * (sep_vals[k] - rbm_vals[k])
            JuMP.add_to_expression!(cut_expr, xi, transcribed_vars[k])
            JuMP.add_to_expression!(cut_expr, -xi * sep_vals[k])
        end
    end
    JuMP.@constraint(transcribed, cut_expr >= 0)
    InfiniteOpt.set_transformation_backend_ready(model, true)
    return
end

end
