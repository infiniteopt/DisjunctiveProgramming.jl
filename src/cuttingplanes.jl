function reformulate_model(
    model::JuMP.AbstractModel, 
    method::cutting_planes
    ) 
    _clear_reformulations(model)
    var_type = JuMP.variable_ref_type(model)
    obj = objective_function(model)
    sense = objective_sense(model)
    SEP, sep_ref_map, _ = copy_gdp_model(model)
    rBM, rBM_ref_map, _ = copy_gdp_model(model)
    reformulate_model(rBM, BigM(method.M_value))
    reformulate_model(SEP, Hull())
    main_to_SEP_map = Dict(v => sep_ref_map[v] for v in all_variables(model))
    main_to_rBM_map = Dict(v => rBM_ref_map[v] for v in all_variables(model))
    JuMP.set_optimizer(SEP, method.optimizer)
    JuMP.set_optimizer(rBM, method.optimizer)
    JuMP.@objective(rBM, sense, 
    _replace_variables_in_constraint(obj, main_to_rBM_map)
    )
    for m in [SEP, rBM]
        binary_vars = filter(is_binary, all_variables(m))
        for var in binary_vars
            unset_binary(var)
            set_lower_bound(var, 0.0)
            set_upper_bound(var, 1.0)
        end
    end

    rBM_to_SEP_map = Dict{var_type, var_type}()
    SEP_to_rBM_map = Dict{var_type, var_type}()
    for (var, rBM_var) in main_to_rBM_map
        SEP_var = main_to_SEP_map[var]
        rBM_to_SEP_map[rBM_var] = SEP_var
        SEP_to_rBM_map[SEP_var] = rBM_var
    end
    
    i = 1
    sep_obj = 1
    while i <= method.max_iter && sep_obj > method.seperation_tolerance
        rBM_sol = _solve_rBM(rBM)
        SEP_sol = _solve_SEP(SEP, rBM, rBM_sol, SEP_to_rBM_map, rBM_to_SEP_map)
        sep_obj = objective_value(SEP)
        _cutting_planes(model, rBM, main_to_rBM_map, 
        main_to_SEP_map, rBM_sol, SEP_sol
        )
        i += 1
    end
    reformulate_model(model, method.final_reform_method)
    return
end

function _solve_rBM(
    rBM::M,
) where {M <: JuMP.AbstractModel}
    T = JuMP.value_type(M)
    JuMP.set_silent(rBM)
    optimize!(rBM, ignore_optimize_hook = true)
    rBM_vars = JuMP.all_variables(rBM)
    sol = Dict{JuMP.AbstractVariableRef, T}(var => zero(T) for var in rBM_vars)
    for rBM_var in rBM_vars
        sol[rBM_var] = JuMP.value(rBM_var)
    end
    return sol
end

function _solve_SEP(
    SEP::M,
    rBM::M,
    rBM_sol::Dict{<:JuMP.AbstractVariableRef, T},
    SEP_to_rBM_map::Dict{<:JuMP.AbstractVariableRef, <:JuMP.AbstractVariableRef},
    rBM_to_SEP_map::Dict{<:JuMP.AbstractVariableRef, <:JuMP.AbstractVariableRef} 
) where {M <: JuMP.AbstractModel, T <: Number}
    JuMP.set_silent(SEP)
    SEP_vars = [rBM_to_SEP_map[rBM_var] for rBM_var in JuMP.all_variables(rBM)]
    obj_expr = sum(
        (SEP_var - rBM_sol[SEP_to_rBM_map[SEP_var]])^2 for SEP_var in SEP_vars
        )
    JuMP.@objective(SEP, Min, obj_expr)

    optimize!(SEP, ignore_optimize_hook = true)

    sol = Dict{JuMP.AbstractVariableRef, T}(var => zero(T) for var in SEP_vars)
    for SEP_var in SEP_vars
        sol[SEP_var] = JuMP.value(SEP_var)
    end
    return sol
end

function _cutting_planes(
    model::M,
    rBM::M,
    main_to_rBM_map::Dict{<:JuMP.AbstractVariableRef, <:JuMP.AbstractVariableRef},
    main_to_SEP_map::Dict{<:JuMP.AbstractVariableRef, <:JuMP.AbstractVariableRef},
    rBM_sol::Dict{<:JuMP.AbstractVariableRef, T},
    SEP_sol::Dict{<:JuMP.AbstractVariableRef, T},
) where {M <: JuMP.AbstractModel, T <: Number}
    main_vars = JuMP.all_variables(model)

    ξ_sep = Dict{JuMP.AbstractVariableRef, T}(var => zero(T) for var in main_vars)
    for var in main_vars
        ξ_sep[var] = 2*(SEP_sol[main_to_SEP_map[var]] - rBM_sol[main_to_rBM_map[var]])
    end
    main_cut = JuMP.@expression(model, 
    sum(ξ_sep[var]*(var - SEP_sol[main_to_SEP_map[var]]) for var in main_vars)
    )
    rBM_cut = _replace_variables_in_constraint(main_cut, main_to_rBM_map)
    JuMP.@constraint(model, main_cut >= 0.0)
    JuMP.@constraint(rBM, rBM_cut >= 0.0)
end

################################################################################
#                              ERROR MESSAGES
################################################################################

function reformulate_model(::M, ::cutting_planes) where {M}
    error("reformulate_model not implemented for model type `$(M)`.")
end

function _solve_rBM(::M) where {M}
    error("_solve_rBM not implemented for model type `$(M)`.")
end

function _solve_SEP(::M, ::N, ::H, ::S, ::R) where {M, N, H, S, R}
    error("_solve_SEP not implemented for argument types:\n
          SEP: `$(M)`, rBM: `$(N)`,\n
          rBM_sol: `$(H)`,\n
          SEP_to_rBM_map: `$(S)`,\n
          rBM_to_SEP_map: `$(R)`.")
end

function _cutting_planes(::M, ::N, ::H, ::S, ::R, ::T) where {M, N, H, S, R, T}
    error("_cutting_planes not implemented for argument types: \n
          model: `$(M)`, rBM: `$(N)`,\n
          main_to_rBM_map: `$(H)`, main_to_SEP_map: 
          `$(S)`,\n
          rBM_sol: `$(R)`,\n
          SEP_sol: `$(T)`.")
end
