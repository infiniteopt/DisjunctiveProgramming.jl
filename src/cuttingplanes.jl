################################################################################
#                       FUNCTIONS FOR LOOP
################################################################################

# Collect decision variables for cutting planes. Extensions may override to
# customize variable collection.
function collect_cutting_planes_vars(model::JuMP.AbstractModel)
    return collect_all_vars(model)
end

# Extract solution from a solved model (in-place). Extensions
# override for models where values live on a backend.
function extract_solution(model::JuMP.AbstractModel)
    dvars = collect_cutting_planes_vars(model)
    V = eltype(dvars)
    T = JuMP.value_type(typeof(model))
    return Dict{V, Vector{T}}(
        v => [JuMP.value(v)] for v in dvars)
end

# Extract solution from a GDPSubmodel (SEP path).
function extract_solution(sub::GDPSubmodel)
    V = eltype(sub.decision_vars)
    T = JuMP.value_type(typeof(sub.model))
    sol = Dict{V, Vector{T}}()
    for var in sub.decision_vars
        sol[var] = JuMP.value.(sub.fwd_map[var])
    end
    return sol
end

# Set quadratic separation objective: min Σ (x_k - rBM_k)².
function _set_separation_objective(
    sub::GDPSubmodel,
    rBM_sol::Dict{<:JuMP.AbstractVariableRef, <:Vector{<:Number}}
    )
    obj_expr = zero(JuMP.GenericQuadExpr{
        JuMP.value_type(typeof(sub.model)),
        JuMP.variable_ref_type(sub.model)}
        )
    for var in sub.decision_vars
        sub_vars = sub.fwd_map[var]
        vals = rBM_sol[var]
        for k in 1:length(sub_vars)
            JuMP.add_to_expression!(obj_expr,
                (sub_vars[k] - vals[k]) *
                (sub_vars[k] - vals[k])
                )
        end
    end
    JuMP.@objective(sub.model, Min, obj_expr)
    return
end

# Solve the separation problem. Returns (separation_obj, separation_sol).
function _solve_separation(
    separation::GDPSubmodel,
    rBM_sol::Dict{<:JuMP.AbstractVariableRef, <:Vector{<:Number}}
    )
    _set_separation_objective(separation, rBM_sol)
    JuMP.optimize!(separation.model, ignore_optimize_hook = true)
    separation_obj = JuMP.objective_value(separation.model)
    separation_sol = extract_solution(separation)
    return separation_obj, separation_sol
end

# Add cut: Σ_var Σ_k 2*(sep_k - rBM_k)*(x_k - sep_k) ≥ 0
function add_cut(
    model::JuMP.AbstractModel,
    decision_vars::Vector{<:JuMP.AbstractVariableRef},
    rBM_sol::Dict{<:JuMP.AbstractVariableRef,<:Vector{<:Number}},
    separation_sol::Dict{<:JuMP.AbstractVariableRef,<:Vector{<:Number}}
    )
    cut_expr = zero(JuMP.GenericAffExpr{
        JuMP.value_type(typeof(model)),
        JuMP.variable_ref_type(model)})
    for var in decision_vars
        rbm_vals = rBM_sol[var]
        sep_vals = separation_sol[var]
        for k in 1:length(rbm_vals)
            xi = 2 * (sep_vals[k] - rbm_vals[k])
            JuMP.add_to_expression!(cut_expr, xi, var)
            JuMP.add_to_expression!(
                cut_expr, -xi * sep_vals[k])
        end
    end
    cref = JuMP.@constraint(model, cut_expr >= 0)
    push!(_reformulation_constraints(model), cref)
    return
end

################################################################################
#                        UNIFIED CUTTING PLANES LOOP
################################################################################

function reformulate_model(
    model::JuMP.AbstractModel,
    method::CuttingPlanes
    )
    _clear_reformulations(model)
    decision_vars = collect_cutting_planes_vars(model)

    # Build separation subproblem from the clean (unreformulated) model
    separation = copy_and_reformulate(model, decision_vars, Hull(), method)
    JuMP.relax_integrality(separation.model)

    # rBM: BigM in-place, relax logical vars
    reformulate_model(model, BigM(method.M_value))
    JuMP.set_optimizer(model, method.optimizer)
    JuMP.set_silent(model)
    relaxed_vars = relax_logical_vars(model)

    # Cutting plane loop: rBM <-> SEP until convergence
    for iter in 1:method.max_iter
        JuMP.optimize!(model, ignore_optimize_hook = true)
        rBM_sol = extract_solution(model)
        separation_obj, separation_sol = _solve_separation(separation, rBM_sol)
        if separation_obj <= method.seperation_tolerance
            break
        end
        add_cut(model, decision_vars, rBM_sol, separation_sol)
    end

    unrelax_logical_vars(relaxed_vars)
    _set_solution_method(model, method)
    _set_ready_to_optimize(model, true)
    return
end

################################################################################
#                              ERROR MESSAGES
################################################################################

function reformulate_model(
    ::M, ::CuttingPlanes
    ) where {M}
    error("reformulate_model not implemented for model type `$(M)`.")
end
