function reformulate_model(
    model::JuMP.AbstractModel, 
    method::cutting_planes
    ) 
    obj = objective_function(model)
    sense = objective_sense(model)
    #Initializing SEP
    SEP = JuMP.Model(method.optimizer)
    _reformulate_disjunctions(model, Hull())
    _reformulate_logical_constraints(model)
    main_to_SEP_map = _copy_variables_and_constraints(model, SEP, method)
    SEP_to_main_map = Dict(v => k for (k, v) in main_to_SEP_map)
    #TODO: Right now there are Invalid Variable Refs. Its harmless but a point to polish at the end
    #EXAMPLE OUTPUT: Dict{AbstractVariableRef, AbstractVariableRef}(InvalidVariableRef => x[1]_Y[2], InvalidVariableRef => x[2]_Y[1], x[2] => x[2], x[1] => x[1], InvalidVariableRef => x[2]_Y[2], Y[1] => Y[1], InvalidVariableRef => x[1]_Y[1], Y[2] => Y[2])
    
    #Initializing rBM
    rBM = JuMP.Model(method.optimizer)
    reformulate_model(model, BigM(10e8))
    main_to_rBM_map = _copy_variables_and_constraints(model, rBM, method)
    JuMP.@objective(rBM, sense, replace_variables_in_constraint(obj, main_to_rBM_map))
    rBM_to_main_map = Dict(v => k for (k, v) in main_to_rBM_map)

    # Create cross-mappings between rBM and SEP models
    rBM_to_SEP_map = Dict{JuMP.AbstractVariableRef, JuMP.AbstractVariableRef}()
    SEP_to_rBM_map = Dict{JuMP.AbstractVariableRef, JuMP.AbstractVariableRef}()
    for (var, rBM_var) in main_to_rBM_map
        SEP_var = main_to_SEP_map[var]
        rBM_to_SEP_map[rBM_var] = SEP_var
        SEP_to_rBM_map[SEP_var] = rBM_var
    end

    for i in range(1, method.iter)
        rBM_sol = _solve_rBM(rBM)
        SEP_sol = _solve_SEP(SEP, rBM, rBM_sol, SEP_to_rBM_map, rBM_to_SEP_map)
        _cutting_planes(model, rBM, main_to_rBM_map, main_to_SEP_map, rBM_sol, SEP_sol)
    end

    _set_solution_method(model, method)
    _set_ready_to_optimize(model, true)
    return
end

function _copy_variables_and_constraints(
    model::JuMP.AbstractModel, 
    target_model::JuMP.AbstractModel,       
    method::cutting_planes
)
    var_map = Dict{JuMP.AbstractVariableRef, JuMP.AbstractVariableRef}()
    for var in JuMP.all_variables(model)
        var_map[var] = _copy_variable(target_model, var, method)
    end
    constraints = JuMP.all_constraints(model; include_variable_in_set_constraints = false)
    for con in [JuMP.constraint_object(con) for con in constraints]
        expr = replace_variables_in_constraint(con.func, var_map)
        JuMP.@constraint(target_model, expr * 1.0 in con.set)
    end
    return var_map
end

function _solve_rBM(
    rBM::JuMP.AbstractModel,
)
    optimize!(rBM)
    rBM_vars = JuMP.all_variables(rBM)
    solution_dict = Dict{JuMP.AbstractVariableRef, Float64}(var => 0.0 for var in rBM_vars)
    for rBM_var in rBM_vars
        solution_dict[rBM_var] = JuMP.value(rBM_var)
    end
    println("rBM OBJECTIVE L = ", objective_value(rBM))
    return solution_dict
end

function _solve_SEP(
    SEP::JuMP.AbstractModel,
    rBM::JuMP.AbstractModel,
    rBM_sol::Dict{JuMP.AbstractVariableRef, Float64},
    SEP_to_rBM_map::Dict{JuMP.AbstractVariableRef, JuMP.AbstractVariableRef},
    rBM_to_SEP_map::Dict{JuMP.AbstractVariableRef, JuMP.AbstractVariableRef} 
)
    SEP_vars = [rBM_to_SEP_map[rBM_var] for rBM_var in JuMP.all_variables(rBM)]
    obj_expr = sum((SEP_var - rBM_sol[SEP_to_rBM_map[SEP_var]])^2 for SEP_var in SEP_vars)
    println("SEP OBJECTIVE L = ", obj_expr)
    JuMP.@objective(SEP, Min, obj_expr)
    optimize!(SEP)

    solution_dict = Dict{JuMP.AbstractVariableRef, Float64}(var => 0.0 for var in SEP_vars)
    for SEP_var in SEP_vars
        solution_dict[SEP_var] = JuMP.value(SEP_var)
    end
    return solution_dict
end

function _cutting_planes(
    model::JuMP.AbstractModel,
    rBM::JuMP.AbstractModel,
    main_to_rBM_map::Dict{JuMP.AbstractVariableRef, JuMP.AbstractVariableRef},
    main_to_SEP_map::Dict{JuMP.AbstractVariableRef, JuMP.AbstractVariableRef},
    rBM_sol::Dict{JuMP.AbstractVariableRef, Float64},
    SEP_sol::Dict{JuMP.AbstractVariableRef, Float64},
)
    main_vars = JuMP.all_variables(model)

    ξ_sep = Dict{JuMP.AbstractVariableRef, Float64}(var => 0.0 for var in main_vars)
    for var in main_vars
        ξ_sep[var] = 2*(SEP_sol[main_to_SEP_map[var]] - rBM_sol[main_to_rBM_map[var]])
    end
    main_cut_expr = JuMP.@expression(model, sum(ξ_sep[var]*(var - SEP_sol[main_to_SEP_map[var]]) for var in main_vars))
    rBM_cut_expr = replace_variables_in_constraint(main_cut_expr, main_to_rBM_map)
    JuMP.@constraint(model, main_cut_expr >= 0)
    JuMP.@constraint(rBM, rBM_cut_expr >= 0)

end
