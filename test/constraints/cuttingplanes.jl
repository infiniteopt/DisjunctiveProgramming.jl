using HiGHS

function test_CuttingPlanes_datatype()
    method = CuttingPlanes(HiGHS.Optimizer)
    @test method.optimizer == HiGHS.Optimizer
    @test method.max_iter == 3
    @test method.seperation_tolerance == 1e-6
    @test method.final_reform_method isa BigM
    @test method.M_value == 1e9

    method = CuttingPlanes(HiGHS.Optimizer;max_iter=10,
    seperation_tolerance=1e-4, final_reform_method=Indicator(), M_value=1e6
    )
    @test method.max_iter == 10
    @test method.seperation_tolerance == 1e-4
    @test method.final_reform_method isa Indicator
    @test method.M_value == 1e6
end

function test_copy_and_reformulate()
    model = GDPModel()
    @variable(model, 0 <= x <= 100)
    @variable(model, Y[1:2], Logical)
    @constraint(model, x <= 3, Disjunct(Y[1]))
    @constraint(model, x <= 4, Disjunct(Y[2]))
    @disjunction(model, [Y[1], Y[2]])
    @objective(model, Max, x)

    method = CuttingPlanes(HiGHS.Optimizer)
    decision_vars = DP.collect_cutting_planes_vars(model)

    # Build SEP subproblem (copy-based)
    separation = DP.copy_and_reformulate(model, decision_vars,
        Hull(), method)

    # GDPSubmodel with decision_vars and fwd_map map
    @test separation isa DP.GDPSubmodel
    @test length(separation.decision_vars) == length(decision_vars)
    @test length(separation.fwd_map) == length(decision_vars)

    # Each fwd_map value is a length-1 vector
    for (var, sub_vars) in separation.fwd_map
        @test length(sub_vars) == 1
        @test sub_vars[1] isa JuMP.VariableRef
    end

    # Subproblem is solvable
    JuMP.relax_integrality(separation.model)
    optimize!(separation.model, ignore_optimize_hook = true)
    @test termination_status(separation.model) == MOI.OPTIMAL
end

function test_reformulate_and_relax()
    model = GDPModel()
    @variable(model, 0 <= x <= 100)
    @variable(model, Y[1:2], Logical)
    @constraint(model, x <= 3, Disjunct(Y[1]))
    @constraint(model, x <= 4, Disjunct(Y[2]))
    @disjunction(model, [Y[1], Y[2]])
    @objective(model, Max, x)

    method = CuttingPlanes(HiGHS.Optimizer)
    decision_vars = DP.collect_cutting_planes_vars(model)

    # Setup rBM on original model (no copy)
    rBM, undo = DP.reformulate_and_relax(model, decision_vars, BigM(method.M_value), method)

    # rBM wraps the original model
    @test rBM isa DP.GDPSubmodel
    @test rBM.model === model
    @test undo !== nothing

    # Identity forward map
    @test length(rBM.fwd_map) == length(decision_vars)
    for v in decision_vars
        @test rBM.fwd_map[v] == [v]
    end

    # Solvable with relaxed integrality
    optimize!(model, ignore_optimize_hook = true)
    @test termination_status(model) == MOI.OPTIMAL

    # Restore integrality
    undo()
end

function test_cp_loop_helpers()
    model = GDPModel()
    @variable(model, 0 <= x <= 100)
    @variable(model, Y[1:2], Logical)
    @constraint(model, x <= 3, Disjunct(Y[1]))
    @constraint(model, x <= 4, Disjunct(Y[2]))
    @disjunction(model, [Y[1], Y[2]])
    @objective(model, Max, x)

    method = CuttingPlanes(HiGHS.Optimizer)
    decision_vars = DP.collect_cutting_planes_vars(model)

    # Build SEP first (from clean model)
    separation = DP.copy_and_reformulate(model, decision_vars,
        Hull(), method)
    JuMP.relax_integrality(separation.model)

    # Setup rBM on original model
    rBM, undo = DP.reformulate_and_relax(model, decision_vars, BigM(method.M_value), method)
    optimize!(model, ignore_optimize_hook = true)

    # Extract solution
    rBM_sol = DP.extract_solution(rBM)
    @test haskey(rBM_sol, x)
    @test length(rBM_sol[x]) == 1

    # Set SEP objective and solve
    DP._set_separation_objective(separation, rBM_sol)
    optimize!(separation.model, ignore_optimize_hook = true)
    @test termination_status(separation.model) == MOI.OPTIMAL

    # SEP solution extraction
    separation_sol = DP.extract_solution(separation)
    @test haskey(separation_sol, x)
    @test separation_sol[x][1] ≈ 4.0 atol = 0.1

    undo()
end

function test_cp_cut_generation()
    model = GDPModel()
    @variable(model, 0 <= x <= 100)
    @variable(model, Y[1:2], Logical)
    @constraint(model, x <= 3, Disjunct(Y[1]))
    @constraint(model, x <= 4, Disjunct(Y[2]))
    @disjunction(model, [Y[1], Y[2]])
    @objective(model, Max, x)

    method = CuttingPlanes(HiGHS.Optimizer)
    decision_vars = DP.collect_cutting_planes_vars(model)

    # Build SEP first (from clean model)
    separation = DP.copy_and_reformulate(model, decision_vars,
        Hull(), method)
    JuMP.relax_integrality(separation.model)

    # Setup rBM on original model, solve
    DP.reformulate_model(model, BigM(method.M_value))
    JuMP.set_optimizer(model, HiGHS.Optimizer)
    JuMP.set_silent(model)
    relaxed = DP.relax_logical_vars(model)
    optimize!(model, ignore_optimize_hook = true)
    rBM_sol = DP._cp_per_support(DP.extract_solution(model))

    # Solve SEP
    DP._set_separation_objective(separation, rBM_sol)
    optimize!(separation.model, ignore_optimize_hook = true)
    separation_sol = DP.extract_solution(separation)

    # Add cut to original model
    num_con_before = length(JuMP.all_constraints(
        model;
        include_variable_in_set_constraints = false
    ))
    DP.add_cut(model, decision_vars, rBM_sol, separation_sol)
    num_con_after = length(JuMP.all_constraints(
        model;
        include_variable_in_set_constraints = false
    ))
    @test num_con_after == num_con_before + 1

    # Re-solve with cut → should tighten
    optimize!(model, ignore_optimize_hook = true)
    rBM_sol2 = DP.extract_solution(model)
    @test rBM_sol2[x] ≈ 4.0 atol = 0.1

    DP.unrelax_logical_vars(relaxed)
end

function test_reformulate_model()
    model = GDPModel()
    @variable(model, 0 <= x[1:4] <= 100)
    @variable(model, Y[1:2], Logical)
    @constraint(model, x[1] + x[2] <= 3, Disjunct(Y[1]))
    @constraint(model, x[3] + x[4] <= 4, Disjunct(Y[2]))
    @disjunction(model, [Y[1], Y[2]])
    @objective(model, Max, x[1] + x[2])

    method = CuttingPlanes(HiGHS.Optimizer)
    DP.reformulate_model(model, method)
    num_con = length(
        JuMP.all_constraints(model; include_variable_in_set_constraints = false)
    )
    # 3 BigM constraints + 0-3 cuts depending on
    # convergence (2 disjunct constraints + 1 exactly-one)
    @test num_con >= 3
    @test_throws ErrorException DP.reformulate_model(42, method)
end


# Maximization where Hull is strictly tighter than BigM,
# forcing many CP iterations with a tight tolerance.
function test_cp_many_iterations()
    model = GDPModel(HiGHS.Optimizer)
    set_silent(model)
    @variable(model, 0 <= x <= 10)
    @variable(model, 0 <= y <= 10)
    @variable(model, Y[1:2], Logical)
    @constraint(model, x + y <= 5, Disjunct(Y[1]))
    @constraint(model, x + y <= 8, Disjunct(Y[2]))
    @disjunction(model, Y)
    @objective(model, Max, x + y)
    cutting_planes = CuttingPlanes(HiGHS.Optimizer;
        max_iter = 50, seperation_tolerance = 1e-10)
    @test optimize!(model, gdp_method = cutting_planes) isa Nothing
    @test termination_status(model) in
        [MOI.OPTIMAL, MOI.LOCALLY_SOLVED]
end

@testset "Cutting Planes" begin
    test_CuttingPlanes_datatype()
    test_copy_and_reformulate()
    test_reformulate_and_relax()
    test_cp_loop_helpers()
    test_cp_cut_generation()
    test_reformulate_model()
    test_cp_many_iterations()
end
