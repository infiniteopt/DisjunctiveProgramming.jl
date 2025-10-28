using HiGHS

function test_cutting_planes_datatype()
    method = cutting_planes(HiGHS.Optimizer)
    @test method.optimizer == HiGHS.Optimizer
    @test method.max_iter == 3
    @test method.tolerance == 1e-6
    @test method.final_reformulation isa BigM
    @test method.M_value == 1e9
    
    method = cutting_planes(HiGHS.Optimizer, 10, 1e-4, Indicator(), 1e6)
    @test method.max_iter == 10
    @test method.tolerance == 1e-4
    @test method.final_reformulation isa Indicator
    @test method.M_value == 1e6
end

function test_copy_variables_and_constraints()
    model = JuMP.Model()
    target_model = JuMP.Model()
    method = cutting_planes(HiGHS.Optimizer)
    @variable(model, x)
    @variable(model, y, Bin)
    
    @constraint(model, x + y <= 1)
    
    var_map = DP._copy_variables_and_constraints(model, target_model, method)
    @test length(var_map) == 2
    @test JuMP.is_binary(var_map[y]) == false
    cons = JuMP.all_constraints(target_model; include_variable_in_set_constraints = false)
    con = JuMP.constraint_object(cons[1])
    @test length(cons) == 1
    new_con = var_map[x] + var_map[y]
    @test con.func == new_con
    @test con.set == MOI.LessThan(1.0)
    
    @test_throws ErrorException DP._copy_variables_and_constraints(model, model, BigM())
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
    method = cutting_planes(HiGHS.Optimizer)
    obj = objective_function(model)
    sense = objective_sense(model)
    DP._reformulate_disjunctions(model, Hull())
    SEP = DP._copy_model(model)
    JuMP.set_optimizer(SEP, method.optimizer)
    DP._reformulate_logical_constraints(model)
    main_to_SEP_map = DP._copy_variables_and_constraints(model, SEP, method)
    DP._clear_reformulations(model)
    DP._reformulate_disjunctions(model, BigM(10e8))
    DP._reformulate_logical_constraints(model)
    rBM = DP._copy_model(model)
    JuMP.set_optimizer(rBM, method.optimizer)
    main_to_rBM_map = DP._copy_variables_and_constraints(model, rBM, method)
    JuMP.@objective(rBM, sense, DP._replace_variables_in_constraint(obj, main_to_rBM_map))
    rBM_to_SEP_map = Dict{JuMP.AbstractVariableRef, JuMP.AbstractVariableRef}()
    SEP_to_rBM_map = Dict{JuMP.AbstractVariableRef, JuMP.AbstractVariableRef}()
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
    method = cutting_planes(HiGHS.Optimizer)
    obj = objective_function(model)
    sense = objective_sense(model)
    DP._reformulate_disjunctions(model, Hull())
    SEP = DP._copy_model(model)
    JuMP.set_optimizer(SEP, method.optimizer)
    DP._reformulate_logical_constraints(model)
    main_to_SEP_map = DP._copy_variables_and_constraints(model, SEP, method)
    DP._clear_reformulations(model)
    DP._reformulate_disjunctions(model, BigM(10e8))
    DP._reformulate_logical_constraints(model)
    rBM = DP._copy_model(model)
    JuMP.set_optimizer(rBM, method.optimizer)
    main_to_rBM_map = DP._copy_variables_and_constraints(model, rBM, method)
    JuMP.@objective(rBM, sense, DP._replace_variables_in_constraint(obj, main_to_rBM_map))
    rBM_to_SEP_map = Dict{JuMP.AbstractVariableRef, JuMP.AbstractVariableRef}()
    SEP_to_rBM_map = Dict{JuMP.AbstractVariableRef, JuMP.AbstractVariableRef}()
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
    test_copy_variables_and_constraints()
    test_solve_rBM()
    test_solve_SEP()
    test_cutting_planes()
    test_reformulate_model()
end
