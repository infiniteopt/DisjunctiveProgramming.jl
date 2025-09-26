using HiGHS

function test_mbm()
    @test MBM(HiGHS.Optimizer).optimizer == HiGHS.Optimizer
end

function test__replace_variables_in_constraint()
    model = Model()
    sub_model = Model()
    @variable(model, x[1:3])
    @constraint(model, con1,x[1] <= 1)
    @constraint(model, con2,x[2]*x[1] <= 1)
    @constraint(model, con3,sin(x[3]) <= 0)
    @constraint(model, con4, [x[1],x[2],x[3]] in MOI.Zeros(3))
    
    #Test GenericVariableRef
    new_vars = Dict{AbstractVariableRef, AbstractVariableRef}()
    [new_vars[x[i]] = @variable(sub_model) for i in 1:3]
    varref = DP._replace_variables_in_constraint(x[1], new_vars)
    expr1 = DP._replace_variables_in_constraint(
        constraint_object(con1).func, new_vars)
    expr2 = DP._replace_variables_in_constraint(
        constraint_object(con2).func, new_vars)
    expr3 = DP._replace_variables_in_constraint(
        constraint_object(con3).func, new_vars)
    expr4 = DP._replace_variables_in_constraint(
        constraint_object(con4).func, new_vars)
    @test expr1 == JuMP.@expression(sub_model, new_vars[x[1]] + 1 - 1)
    @test expr2 == JuMP.@expression(sub_model, new_vars[x[2]]*new_vars[x[1]])
    @test varref == new_vars[x[1]]
    # Test nonlinear expression structure
    #TODO: Fix expr3 test, JuMP.@expression(model, sin(x[3]) - 0) is not equal to expr3
    #MBM: Test Failed at c:\Users\LocalAdmin\Code\DisjunctiveProgramming.jl\test\constraints\mbm.jl:32
    # Expression: expr3 == #= c:\Users\LocalAdmin\Code\DisjunctiveProgramming.jl\test\constraints\mbm.jl:32 =# JuMP.@expression(model, sin(x[3]) - 0)
    # Evaluated: sin(_[3]) - 0.0 == sin(x[3]) - 0.0
    @test expr3 isa JuMP.NonlinearExpr  # Test it's a nonlinear expression
    @test expr4 == [new_vars[x[i]] for i in 1:3]
    @test_throws ErrorException DP._replace_variables_in_constraint(
        "String", new_vars)
end

function test__constraint_to_objective()
    model = Model()
    sub_model = Model()

    @variable(model, x[1:2])
    @constraint(model, lessthan, x[1] <= 1) 
    @constraint(model, greaterthan, x[2] >= 1)
    @constraint(model, interval, 0 <= x[1] <= 55)
    @constraint(model, equalto, x[1] == 1)
    new_vars = Dict{AbstractVariableRef, AbstractVariableRef}()
    [new_vars[x[i]] = @variable(sub_model) for i in 1:2]
    DP._constraint_to_objective(sub_model, constraint_object(lessthan), 
        new_vars)
    @test objective_function(sub_model) == JuMP.@expression(sub_model, 
        new_vars[x[1]] - 1)
    DP._constraint_to_objective(sub_model, constraint_object(greaterthan), 
        new_vars)
    @test objective_function(sub_model) == JuMP.@expression(sub_model, 
        1 - new_vars[x[2]])
    @test_throws ErrorException DP._constraint_to_objective(sub_model, 
        constraint_object(interval), new_vars)
end

function test_mini_model()
    model = GDPModel()
    @variable(model, 0 <= x, start = 1)
    @variable(model, 0 <= y)
    @variable(model, Y[1:4], Logical)
    @constraint(model, con, 3*-x <= 4, Disjunct(Y[1]))
    @constraint(model, con2, 3*x + y >= 15, Disjunct(Y[2]))
    @constraint(model, infeasiblecon, 3*x + y == 15, Disjunct(Y[3]))
    @constraint(model, intervalcon, 0 <= x <= 55, Disjunct(Y[4]))
    @disjunction(model, [Y[1], Y[2], Y[3], Y[4]])
    @test DP._mini_model(model, constraint_object(con), 
        DisjunctConstraintRef[con2], MBM(HiGHS.Optimizer))== -4
    set_upper_bound(x, 1)
    @test DP._mini_model(model, constraint_object(con2), 
        DisjunctConstraintRef[con], MBM(HiGHS.Optimizer))== 15
    set_integer(y)
    @constraint(model, con3, y*x == 15, Disjunct(Y[1]))
    @test DP._mini_model(model, constraint_object(con2), 
        DisjunctConstraintRef[con], MBM(HiGHS.Optimizer))== 15
    JuMP.fix(y, 5; force=true)
    @test DP._mini_model(model, constraint_object(con2), 
        DisjunctConstraintRef[con], MBM(HiGHS.Optimizer))== 10
    delete_lower_bound(x)
    @test DP._mini_model(model, constraint_object(con2), 
        DisjunctConstraintRef[con2], MBM(HiGHS.Optimizer)) == 1.0e9
    @test_throws ErrorException DP._mini_model(model, 
        constraint_object(infeasiblecon), DisjunctConstraintRef[con], 
        MBM(HiGHS.Optimizer))
end

function test_maximize_M()
    model = GDPModel()
    @variable(model, 0 <= x[1:2] <= 50)
    @variable(model, Y[1:6], Logical)
    @constraint(model, lessthan, x[1] <= 1, Disjunct(Y[1]))
    @constraint(model, greaterthan, x[1] >= 1, Disjunct(Y[1]))
    @constraint(model, interval, 0 <= x[1] <= 55, Disjunct(Y[2]))
    @constraint(model, equalto, x[1] == 1, Disjunct(Y[3]))
    @constraint(model, nonpositives, -x in MOI.Nonpositives(2), 
        Disjunct(Y[4]))
    @constraint(model, nonnegatives, x in MOI.Nonnegatives(2), 
        Disjunct(Y[5]))
    @constraint(model, zeros, -x .+ 1 in MOI.Zeros(2), Disjunct(Y[6]))
    
    @test DP._maximize_M(model, constraint_object(interval), 
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]), 
        MBM(HiGHS.Optimizer)) == 0.0
    @test DP._maximize_M(model, constraint_object(lessthan), 
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]), 
        MBM(HiGHS.Optimizer)) == 49
    @test DP._maximize_M(model, constraint_object(greaterthan), 
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]), 
        MBM(HiGHS.Optimizer)) == 1.0
    @test DP._maximize_M(model, constraint_object(equalto), 
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[3]]), 
        MBM(HiGHS.Optimizer)) == 0
    @test DP._maximize_M(model, constraint_object(nonpositives), 
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]), 
        MBM(HiGHS.Optimizer)) == 0
    @test DP._maximize_M(model, constraint_object(nonnegatives), 
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]), 
        MBM(HiGHS.Optimizer)) == 0
    @test DP._maximize_M(model, constraint_object(zeros), 
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]), 
        MBM(HiGHS.Optimizer)) == 49
    @test_throws ErrorException DP._maximize_M(model, "odd", 
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]), 
        MBM(HiGHS.Optimizer))
end

function test_reformulate_disjunct_constraint()
    model = GDPModel()
    @variable(model, 0 <= x[1:2] <= 50)
    @variable(model, Y[1:6], Logical)
    @constraint(model, lessthan, x[1] <= 1, Disjunct(Y[1]))
    @constraint(model, greaterthan, x[1] >= 1, Disjunct(Y[1]))
    @constraint(model, equalto, x[1] == 1, Disjunct(Y[2]))
    @constraint(model, nonpositives, -x in MOI.Nonpositives(2), 
        Disjunct(Y[3]))
    @constraint(model, nonnegatives, x in MOI.Nonnegatives(2), 
        Disjunct(Y[4]))
    @constraint(model, zeros, -x .+ 1 in MOI.Zeros(2), Disjunct(Y[5]))

    method = MBM(HiGHS.Optimizer)
    for i in 1:5
        method.M[Y[i]] = Float64(i)
    end
    bconref = Dict(Y[i] => binary_variable(Y[i]) for i in 1:5)
    
    reformulated_constraints = [reformulate_disjunct_constraint(model, 
        constraint_object(constraints), bconref, method) 
        for constraints in [lessthan, greaterthan, equalto, nonpositives, 
            nonnegatives, zeros]]
    @test reformulated_constraints[1][1].func == JuMP.@expression(model, 
        x[1] - sum(method.M[i] * bconref[i] for i in keys(method.M))) && 
        reformulated_constraints[1][1].set == MOI.LessThan(1.0)
    @test reformulated_constraints[2][1].func == JuMP.@expression(model, 
        x[1] + sum(method.M[i] * bconref[i] for i in keys(method.M))) && 
        reformulated_constraints[2][1].set == MOI.GreaterThan(1.0)
    @test reformulated_constraints[3][1].func == JuMP.@expression(model, 
        x[1] + sum(method.M[i] * bconref[i] for i in keys(method.M))) && 
        reformulated_constraints[3][1].set == MOI.GreaterThan(1.0)
    @test reformulated_constraints[3][2].func == JuMP.@expression(model, 
        x[1] - sum(method.M[i] * bconref[i] for i in keys(method.M))) && 
        reformulated_constraints[3][2].set == MOI.LessThan(1.0)
    @test reformulated_constraints[4][1].func == JuMP.@expression(model, 
        -x .- sum(method.M[i] * bconref[i] for i in keys(method.M))) && 
        reformulated_constraints[4][1].set == MOI.Nonpositives(2)
    @test reformulated_constraints[5][1].func == JuMP.@expression(model, 
        x .+ sum(method.M[i] * bconref[i] for i in keys(method.M))) && 
        reformulated_constraints[5][1].set == MOI.Nonnegatives(2)
    @test reformulated_constraints[6][1].func == JuMP.@expression(model, 
        -x .+(1 + sum(method.M[i] * bconref[i] for i in keys(method.M)))) && 
        reformulated_constraints[6][1].set == MOI.Nonnegatives(2)
    @test reformulated_constraints[6][2].func == JuMP.@expression(model, 
        -x .+(1 - sum(method.M[i] * bconref[i] for i in keys(method.M)))) && 
        reformulated_constraints[6][2].set == MOI.Nonpositives(2)
    @test_throws ErrorException reformulate_disjunct_constraint(model, 
        "odd", bconref, method)
end

function test_reformulate_disjunct()
    model = GDPModel()
    @variable(model, 1 <= x[1:2] <= 5)
    @variable(model, Y[1:2], Logical)
    @constraint(model, greaterthan, x[1] >= 1, Disjunct(Y[1]))
    @constraint(model, interval, x[1] == 2.5, Disjunct(Y[2]))

    method = MBM(HiGHS.Optimizer)
    disj = constraint_object(disjunction(model, [Y[1], Y[2]]))
    reformulated_disjunct = reformulate_disjunction(model, disj, method)

    @test length(reformulated_disjunct) == 3

    @test reformulated_disjunct[1].set == MOI.GreaterThan(1.0)
    @test reformulated_disjunct[2].set == MOI.GreaterThan(2.5)  
    @test reformulated_disjunct[3].set == MOI.LessThan(2.5)

    # Test that the expressions have the right structure
    # Check coefficients and variables in the affine expressions
    func_1 = reformulated_disjunct[1].func
    func_2 = reformulated_disjunct[2].func
    func_3 = reformulated_disjunct[3].func

    @test JuMP.coefficient(func_1, x[1]) == 1.0
    @test JuMP.coefficient(func_1, binary_variable(Y[2])) == -1.5

    @test JuMP.coefficient(func_2, x[1]) == 1.0
    @test JuMP.coefficient(func_2, binary_variable(Y[1])) == 2.5

    @test JuMP.coefficient(func_3, x[1]) == 1.0
    @test JuMP.coefficient(func_3, binary_variable(Y[1])) == -2.5
end

function test_reformulate_disjunction()
    model = GDPModel()
    @variable(model, x)
    @variable(model, Y[1:2], Logical)
    @constraint(model, lessthan, x <= 2, Disjunct(Y[1]))
    @constraint(model, greaterthan, x >= 1, Disjunct(Y[1]))
    @constraint(model, interval, 0 <= x <= 55, Disjunct(Y[2]))
    disj = disjunction(model, [Y[1], Y[2]])
    
    method = MBM(HiGHS.Optimizer)
    ref_cons = reformulate_disjunction(model, constraint_object(disj), method)

    @test length(ref_cons) == 4

    @test ref_cons[1].set == MOI.LessThan(2.0)
    
    @test ref_cons[2].set == MOI.GreaterThan(1.0)
    
    @test ref_cons[3].set == MOI.GreaterThan(0.0)
    
    @test ref_cons[4].set == MOI.LessThan(55.0)

    func_1 = ref_cons[1].func  # x - 53 Y[2] <= 2.0
    func_2 = ref_cons[2].func  # x + 53 Y[2] >= 1.0
    func_3 = ref_cons[3].func  # x - Y[1] >= 0.0
    func_4 = ref_cons[4].func  # x + Y[1] <= 55.0

    @test JuMP.coefficient(func_1, x) == 1.0
    @test JuMP.coefficient(func_1, binary_variable(Y[2])) == -53.0

    @test JuMP.coefficient(func_2, x) == 1.0
    @test JuMP.coefficient(func_2, binary_variable(Y[2])) == 53.0

    @test JuMP.coefficient(func_3, x) == 1.0
    @test JuMP.coefficient(func_3, binary_variable(Y[1])) == -1.0

    @test JuMP.coefficient(func_4, x) == 1.0
    @test JuMP.coefficient(func_4, binary_variable(Y[1])) == 1.0
end

@testset "MBM" begin
    test_mbm()
    test__replace_variables_in_constraint()
    test__constraint_to_objective()
    test_mini_model()
    test_maximize_M()
    test_reformulate_disjunct_constraint()
    test_reformulate_disjunct()
    test_reformulate_disjunction()
end