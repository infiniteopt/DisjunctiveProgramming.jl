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

# Quadratic expression: handle parameter x parameter, parameter x variable,
# and variable x variable terms.
function DP.disaggregate_expression(
    model::M, quad::JuMP.GenericQuadExpr,
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::DP._Hull
    ) where {M <: InfiniteOpt.InfiniteModel}
    # Affine part (uses InfiniteOpt override above)
    new_expr = DP.disaggregate_expression(model, quad.aff, bvref, method)
    ϵ = method.value
    for (pair, coeff) in quad.terms
        a_param = pair.a isa InfiniteOpt.GeneralVariableRef &&
            _is_parameter(pair.a)
        b_param = pair.b isa InfiniteOpt.GeneralVariableRef &&
            _is_parameter(pair.b)
        if a_param && b_param
            # param × param: constant, scale by y
            new_expr += coeff * pair.a * pair.b * bvref
        elseif a_param
            # param × var: perspective cancels y
            db = method.disjunct_variables[pair.b, bvref]
            new_expr += coeff * pair.a * db
        elseif b_param
            # var × param: perspective cancels y
            da = method.disjunct_variables[pair.a, bvref]
            new_expr += coeff * da * pair.b
        else
            # var × var: standard perspective
            da = method.disjunct_variables[pair.a, bvref]
            db = method.disjunct_variables[pair.b, bvref]
            new_expr += coeff * da * db / ((1 - ϵ) * bvref + ϵ)
        end
    end
    return new_expr
end

################################################################################
#                          MBM FOR INFINITEMODEL
################################################################################
# Reuses the finite MBM infrastructure by overriding:
# copy_model_with_constraints (build mini InfiniteModel +
# transcribe to flat JuMP model), prepare_max_M_objective
# (expand infinite constraint into K flat objectives via
# _build_flat_map), and raw_M (vector dispatch aggregates
# K per-support M values into a parameter function).

# Collect all parameter function refs from all disjunct constraints in
# the model.
function _all_param_functions(
    model::InfiniteOpt.InfiniteModel
    )
    pf_set = Set{InfiniteOpt.GeneralVariableRef}()
    for (_, crefs) in DP._indicator_to_constraints(model)
        for cref in crefs
            cref isa DP.DisjunctConstraintRef || continue
            con = JuMP.constraint_object(cref)
            for v in InfiniteOpt.all_expression_variables(con.func)
                dv = InfiniteOpt.dispatch_variable_ref(v)
                if dv isa InfiniteOpt.ParameterFunctionRef
                    push!(pf_set, v)
                end
            end
        end
    end
    return pf_set
end

# Build a flat map for support point k. Maps decision variables to their
# flat JuMP.VariableRef at support k (handling multi-parameter indexing)
# and evaluates parameter functions to their numerical values. pf_set is
# precomputed by the caller to avoid rescanning all disjunct constraints
# on every support point.
function _build_flat_map(
    sub::DP.GDPSubmodel, k::Int,
    prefs::Vector{InfiniteOpt.GeneralVariableRef},
    supports::Dict{InfiniteOpt.GeneralVariableRef, Vector{Float64}},
    full_shape::Tuple,
    pf_set::Set{InfiniteOpt.GeneralVariableRef}
    )
    ci = CartesianIndices(full_shape)[k]

    # Decision variables: map each to its variable-local index
    flat_map = Dict{InfiniteOpt.GeneralVariableRef, Any}()
    for (v, ws) in sub.fwd_map
        if length(ws) == 1
            flat_map[v] = only(ws)
        else
            vp = InfiniteOpt.parameter_refs(v)
            shape = Tuple(length(supports[p]) for p in vp)
            idx = Tuple(ci[findfirst(==(p), prefs)] for p in vp)
            flat_map[v] = ws[LinearIndices(shape)[idx...]]
        end
    end

    # Parameter functions: evaluate at support point k
    sup_vals = Dict(
        prefs[i] => supports[prefs[i]][ci[i]]
        for i in 1:length(prefs))
    for pf in pf_set
        fn = InfiniteOpt.raw_function(pf)
        pf_prefs = InfiniteOpt.parameter_refs(pf)
        pf_vals = Tuple(sup_vals[p] for p in pf_prefs)
        flat_map[pf] = fn(pf_vals...)
    end
    return flat_map
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
        sups = Float64.(InfiniteOpt.supports(p))
        param = InfiniteOpt.build_parameter(error, domain; supports = sups)
        new_p = InfiniteOpt.add_parameter(mini, param, JuMP.name(p))
        ref_map[p] = new_p
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
    pf_set = _all_param_functions(model)
    for pf in pf_set
        fn = InfiniteOpt.raw_function(pf)
        prefs = InfiniteOpt.parameter_refs(pf)
        mapped_prefs = Tuple(ref_map[p] for p in prefs)
        new_pf = _make_parameter_function(mini, fn, mapped_prefs...)
        ref_map[pf] = new_pf
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
    tr_fwd = Dict{InfiniteOpt.GeneralVariableRef,
        Vector{JuMP.VariableRef}}()
    for v in DP.collect_all_vars(mini)
        tv = InfiniteOpt.transformation_variable(v)
        vprefs = InfiniteOpt.parameter_refs(v)
        tr_fwd[v] = isempty(vprefs) ? [tv] : vec(tv)
    end

    # 7. Remap fwd_map: original model var -> flat JuMP VarRef
    fwd_map = Dict{InfiniteOpt.GeneralVariableRef, Vector{JuMP.VariableRef}}()
    for (orig, mapped) in ref_map
        _is_parameter(orig) && continue
        haskey(tr_fwd, mapped) || continue
        fwd_map[orig] = tr_fwd[mapped]
    end

    decision_vars = collect(keys(fwd_map))
    JuMP.set_optimizer(flat, method.optimizer)
    JuMP.set_silent(flat)
    return DP.GDPSubmodel(flat, decision_vars, fwd_map)
end

# Prepare objectives for all support points. Expands an infinite
# constraint into K flat objectives via _build_flat_map with
# multi-parameter indexing and parameter function evaluation.
function DP.prepare_max_M_objective(
    model::InfiniteOpt.InfiniteModel,
    obj::JuMP.ScalarConstraint{T, S},
    sub::DP.GDPSubmodel
    ) where {T, S <: _MOI.LessThan}
    prefs, supports = _collect_parameters(model)
    full_shape = Tuple(length(supports[p]) for p in prefs)
    K = prod(full_shape)
    pf_set = _all_param_functions(model)
    objectives = Vector{JuMP.AbstractJuMPScalar}(undef, K)
    for k in 1:K
        flat_map = _build_flat_map(sub, k, prefs, supports, full_shape, pf_set)
        objectives[k] = -obj.set.upper +
            DP._replace_variables_in_constraint(obj.func, flat_map)
    end
    return objectives
end

function DP.prepare_max_M_objective(
    model::InfiniteOpt.InfiniteModel,
    obj::JuMP.ScalarConstraint{T, S},
    sub::DP.GDPSubmodel
    ) where {T, S <: _MOI.GreaterThan}
    prefs, supports = _collect_parameters(model)
    full_shape = Tuple(length(supports[p]) for p in prefs)
    K = prod(full_shape)
    pf_set = _all_param_functions(model)
    objectives = Vector{JuMP.AbstractJuMPScalar}(undef, K)
    for k in 1:K
        flat_map = _build_flat_map(sub, k, prefs, supports, full_shape, pf_set)
        objectives[k] = obj.set.lower -
            DP._replace_variables_in_constraint(obj.func, flat_map)
    end
    return objectives
end

# Solve the submodel for a vector of objectives (one per support point).
# Returns aggregated M value (scalar or parameter function) or nothing.
function DP.raw_M(
    sub::DP.GDPSubmodel,
    objectives::Vector{<:JuMP.AbstractJuMPScalar},
    method::DP._MBM
    )
    M_vals = typeof(method.default_M)[]
    for obj_expr in objectives
        JuMP.set_start_value.(JuMP.all_variables(sub.model), nothing)
        JuMP.@objective(sub.model, Max, obj_expr)
        JuMP.optimize!(sub.model)
        if JuMP.is_solved_and_feasible(sub.model)
            push!(M_vals, max(
                JuMP.objective_value(sub.model),
                zero(method.default_M)))
        elseif JuMP.termination_status(sub.model) ==
                JuMP.MOI.INFEASIBLE
            return nothing
        else
            push!(M_vals, method.default_M)
        end
    end
    model = JuMP.owner_model(first(keys(sub.fwd_map)))
    # Condense flat per-support values: scalar if uniform, else pf.
    all(==(M_vals[1]), M_vals) && return M_vals[1]
    prefs, supports = _collect_parameters(model)
    grids = Tuple(supports[p] for p in prefs)
    shape = Tuple(length(supports[p]) for p in prefs)
    fn = Interpolations.linear_interpolation(
        grids, reshape(M_vals, shape),
        extrapolation_bc = Interpolations.Line())
    return _make_parameter_function(model, fn, prefs...)
end

################################################################################
#                          TRANSCRIPTION HELPERS
################################################################################

# Replacement for @parameter_function in the case of using an interpolation.
# Example (1D interpolation):
#   fn = Interpolations.linear_interpolation(grids, vals)
#   pf = _make_parameter_function(model, fn, t)  # returns a pf ref
function _make_parameter_function(
    model::InfiniteOpt.InfiniteModel, fn,
    prefs::InfiniteOpt.GeneralVariableRef...
    )
    f = fn isa Function ? fn : ((args...) -> fn(args...))
    pref_arg = length(prefs) == 1 ? only(prefs) : prefs
    pfunc = InfiniteOpt.build_parameter_function(error, f, pref_arg)
    return InfiniteOpt.add_parameter_function(model, pfunc)
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
    tr_fwd = Dict{InfiniteOpt.GeneralVariableRef,
        Vector{JuMP.VariableRef}}()
    for v in DP.collect_all_vars(model)
        tv = InfiniteOpt.transformation_variable(v)
        vprefs = InfiniteOpt.parameter_refs(v)
        tr_fwd[v] = isempty(vprefs) ? [tv] : vec(tv)
    end
    sub_copy, copy_map = JuMP.copy_model(flat)
    fwd_map = Dict{InfiniteOpt.GeneralVariableRef,
        Vector{JuMP.VariableRef}}()
    for v in decision_vars
        haskey(tr_fwd, v) || continue
        fwd_map[v] = [copy_map[tv] for tv in tr_fwd[v]]
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
        tv = InfiniteOpt.transformation_variable(v)
        vprefs = InfiniteOpt.parameter_refs(v)
        sol[v] = isempty(vprefs) ? [JuMP.value(tv)] : JuMP.value.(vec(tv))
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
        tv = InfiniteOpt.transformation_variable(var)
        flat_vars = tv isa AbstractArray ? vec(tv) : [tv]
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
