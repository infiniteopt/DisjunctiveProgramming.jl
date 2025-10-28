function reformulate_model(
    model::JuMP.AbstractModel, 
    method::cutting_planes
    ) 
    var_type = JuMP.variable_ref_type(model)
    obj = objective_function(model)
    sense = objective_sense(model)
    #Seperation Model
    _reformulate_disjunctions(model, Hull())
    SEP = _copy_model(model)
    JuMP.set_optimizer(SEP, method.optimizer)
    _reformulate_logical_constraints(model)
    main_to_SEP_map = _copy_variables_and_constraints(model, SEP, method)
    #Relaxed BigM model
    _clear_reformulations(model)
    _reformulate_disjunctions(model, BigM(method.M_value))
    _reformulate_logical_constraints(model)
    rBM = _copy_model(model)
    JuMP.set_optimizer(rBM, method.optimizer)
    main_to_rBM_map = _copy_variables_and_constraints(model, rBM, method)
    JuMP.@objective(rBM, sense, 
    _replace_variables_in_constraint(obj, main_to_rBM_map)
    )

    rBM_to_SEP_map = Dict{var_type, var_type}()
    SEP_to_rBM_map = Dict{var_type, var_type}()
    for (var, rBM_var) in main_to_rBM_map
        SEP_var = main_to_SEP_map[var]
        rBM_to_SEP_map[rBM_var] = SEP_var
        SEP_to_rBM_map[SEP_var] = rBM_var
    end

    i = 1
    sep_obj = 1
    while i <= method.max_iter && sep_obj > method.tolerance
        rBM_sol = _solve_rBM(rBM)
        SEP_sol = _solve_SEP(SEP, rBM, rBM_sol, SEP_to_rBM_map, rBM_to_SEP_map)
        sep_obj = objective_value(SEP)
        _cutting_planes(model, rBM, main_to_rBM_map, 
        main_to_SEP_map, rBM_sol, SEP_sol
        )
        i += 1
    end
    reformulate_model(model, method.final_reformulation)
    return
end

function _copy_variables_and_constraints(
    model::M, 
    target_model::M,       
    method::cutting_planes
) where {M <: JuMP.AbstractModel}
    T = JuMP.value_type(M)
    var_type = JuMP.variable_ref_type(model)

    var_map = Dict{var_type, var_type}()
    for var in JuMP.all_variables(model)
        props = VariableProperties(var)
        if props.info.binary
            info = JuMP.VariableInfo(
                true, zero(T),    
                true, one(T),    
                false, zero(T),   
                props.info.has_start, props.info.start,  
                false,        
                false         
            )
            props = VariableProperties(
                info,
                props.name,
                nothing,  # Clear any binary set
                props.variable_type
            )
            new_var = create_variable(target_model, props)
            var_map[var] = new_var
        else
            new_var = variable_copy(target_model, var)
            var_map[var] = new_var
        end
    end
    constraints = JuMP.all_constraints(model; 
    include_variable_in_set_constraints = false
    )
    for con in [JuMP.constraint_object(con) for con in constraints]        
        expr = _replace_variables_in_constraint(con.func, var_map)
        JuMP.@constraint(target_model, expr * 1.0 in con.set)
    end
    return var_map
end

function _solve_rBM(
    rBM::M,
) where {M <: JuMP.AbstractModel}
    T = JuMP.value_type(M)
    JuMP.set_silent(rBM)
    optimize!(rBM)
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

    optimize!(SEP)

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

function reformulate_model(model, method::cutting_planes)
    error("reformulate_model not implemented for model type `$(typeof(model))`.")
end

function _copy_variables_and_constraints(model, target_model, method)
    error("_copy_variables_and_constraints not implemented for model types
          `$(typeof(model))`, `$(typeof(target_model))`. 
          Both model types much match."
          )
end

function _solve_rBM(model)
    error("_solve_rBM not implemented for model type `$(typeof(model))`.")
end

function _solve_SEP(SEP, rBM, rBM_sol, SEP_to_rBM_map, rBM_to_SEP_map)
    error("_solve_SEP not implemented for argument types:\n
          SEP: `$(typeof(SEP))`, rBM: `$(typeof(rBM))`,\n
          rBM_sol: `$(typeof(rBM_sol))`,\n
          SEP_to_rBM_map: `$(typeof(SEP_to_rBM_map))`,\n
          rBM_to_SEP_map: `$(typeof(rBM_to_SEP_map))`.")
end

function _cutting_planes(model, rBM, main_to_rBM_map, main_to_SEP_map, rBM_sol, SEP_sol)
    error("_cutting_planes not implemented for argument types: \n
          model: `$(typeof(model))`, rBM: `$(typeof(rBM))`,\n
          main_to_rBM_map: `$(typeof(main_to_rBM_map))`, main_to_SEP_map: `$(typeof(main_to_SEP_map))`,\n
          rBM_sol: `$(typeof(rBM_sol))`, SEP_sol: `$(typeof(SEP_sol))`.")
end
