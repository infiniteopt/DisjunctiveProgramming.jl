using HiGHS

function test_cutting_planes_datatype()
    method = cutting_planes(HiGHS.Optimizer)
    @test method.optimizer == HiGHS.Optimizer
    @test method.max_iter == 3
    @test method.seperation_tolerance == 1e-6
    @test method.final_reform_method isa BigM
    @test method.M_value == 1e9
    
    method = cutting_planes(HiGHS.Optimizer;max_iter=10, 
    seperation_tolerance=1e-4, final_reform_method=Indicator(), M_value=1e6
    )
    @test method.max_iter == 10
    @test method.seperation_tolerance == 1e-4
    @test method.final_reform_method isa Indicator
    @test method.M_value == 1e6
end

function test_solve_rBM()
    rBM = JuMP.Model(HiGHS.Optimizer)
    @variable(rBM, 0 <= x <= 100)
    @variable(rBM, 0 <= y[1:2] <= 1)
    @constraint(rBM, x <= 3 + 100(1 - y[1]))
    @constraint(rBM, x <= 4 + 100(1 - y[2]))
    @constraint(rBM, y[1] + y[2] == 1)
    @objective(rBM, Max, x)

    solutions = DP._solve_rBM(rBM)
    @test solutions[x] == 53.5
    @test solutions[y[1]] == 0.495
    @test solutions[y[2]] == 0.505
    
    @test_throws ErrorException DP._solve_rBM(Dict())
end

function test_solve_SEP()
    model = GDPModel()
    @variable(model, 0 <= x <= 100)
    @variable(model, Y[1:2], Logical)
    @constraint(model, x <= 3, Disjunct(Y[1]))
    @constraint(model, x <= 4, Disjunct(Y[2]))
    @disjunction(model, [Y[1], Y[2]])
    @objective(model, Max, x)
    var_type = JuMP.variable_ref_type(model)
    method = cutting_planes(HiGHS.Optimizer)
    obj = objective_function(model)
    sense = objective_sense(model)
    SEP, sep_ref_map, _ = DP.copy_gdp_model(model)
    rBM, rBM_ref_map, _ = DP.copy_gdp_model(model)
    DP.reformulate_model(rBM, DP.BigM(method.M_value))
    DP.reformulate_model(SEP, DP.Hull())
    main_to_SEP_map = Dict(v => sep_ref_map[v] for v in all_variables(model))
    main_to_rBM_map = Dict(v => rBM_ref_map[v] for v in all_variables(model))
    JuMP.set_optimizer(SEP, method.optimizer)
    JuMP.set_optimizer(rBM, method.optimizer)
    JuMP.@objective(rBM, sense, 
    DP._replace_variables_in_constraint(obj, main_to_rBM_map)
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
    rBM_sol = DP._solve_rBM(rBM)
    SEP_sol = DP._solve_SEP(SEP, rBM, rBM_sol, SEP_to_rBM_map, rBM_to_SEP_map)
    @test length(SEP_sol) == length(rBM_sol)
    @test SEP_sol[rBM_to_SEP_map[main_to_rBM_map[x]]] ≈ 4.0
    
    @test_throws ErrorException DP._solve_SEP(SEP, rBM, rBM_sol, SEP_to_rBM_map, "not a dict")
end

function test_cutting_planes()
    model = GDPModel()
    @variable(model, 0 <= x <= 100)
    @variable(model, Y[1:2], Logical)
    @constraint(model, x <= 3, Disjunct(Y[1]))
    @constraint(model, x <= 4, Disjunct(Y[2]))
    @disjunction(model, [Y[1], Y[2]])
    @objective(model, Max, x)
    var_type = JuMP.variable_ref_type(model)
    method = cutting_planes(HiGHS.Optimizer)
    obj = objective_function(model)
    sense = objective_sense(model)
    SEP, sep_ref_map, _ = DP.copy_gdp_model(model)
    rBM, rBM_ref_map, _ = DP.copy_gdp_model(model)
    DP.reformulate_model(rBM, DP.BigM(method.M_value))
    DP.reformulate_model(SEP, DP.Hull())
    main_to_SEP_map = Dict(v => sep_ref_map[v] for v in all_variables(model))
    main_to_rBM_map = Dict(v => rBM_ref_map[v] for v in all_variables(model))
    JuMP.set_optimizer(SEP, method.optimizer)
    JuMP.set_optimizer(rBM, method.optimizer)
    JuMP.@objective(rBM, sense, 
    DP._replace_variables_in_constraint(obj, main_to_rBM_map)
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
    rBM_sol = DP._solve_rBM(rBM)
    SEP_sol = DP._solve_SEP(SEP, rBM, rBM_sol, SEP_to_rBM_map, rBM_to_SEP_map)
    DP._cutting_planes(model, rBM, main_to_rBM_map, main_to_SEP_map, rBM_sol, SEP_sol)

    rBM_sol = DP._solve_rBM(rBM)
    SEP_sol = DP._solve_SEP(SEP, rBM, rBM_sol, SEP_to_rBM_map, rBM_to_SEP_map)

    @test rBM_sol[main_to_rBM_map[x]] ≈ 4.0
    @test SEP_sol[rBM_to_SEP_map[main_to_rBM_map[x]]] ≈ 4.0 atol=1e-3
    
    @test_throws ErrorException DP._cutting_planes(model, rBM, main_to_rBM_map, main_to_SEP_map, rBM_sol, "not a dict")
end

function test_reformulate_model()
    model = GDPModel()
    @variable(model, 0 <= x[1:4] <= 100)
    @variable(model, Y[1:2], Logical)
    @constraint(model, x[1] + x[2] <= 3, Disjunct(Y[1]))
    @constraint(model, x[3] + x[4] <= 4, Disjunct(Y[2]))
    @disjunction(model, [Y[1], Y[2]])
    @objective(model, Max, x[1] + x[2])

    method = cutting_planes(HiGHS.Optimizer)
    DP.reformulate_model(model, method)
    num_con = length(
        JuMP.all_constraints(model; include_variable_in_set_constraints = false)
    )
    @test num_con == 4
    @test_throws ErrorException DP.reformulate_model(42, method)
end


@testset "Cutting Planes" begin
    test_cutting_planes_datatype()
    test_solve_rBM()
    test_solve_SEP()
    test_cutting_planes()
    test_reformulate_model()
end
