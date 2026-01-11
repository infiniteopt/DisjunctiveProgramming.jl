using HiGHS

function test_mbm()

    @test DP._MBM(
        DP.MBM(HiGHS.Optimizer), JuMP.Model()
    ).optimizer == HiGHS.Optimizer

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
    @test expr3 isa JuMP.NonlinearExpr
    expected = JuMP.@expression(sub_model, sin(new_vars[x[3]]) - 0.0)
    @test JuMP.isequal_canonical(expr3, expected)
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
    mbm = DP._MBM(DP.MBM(HiGHS.Optimizer), JuMP.Model())
    @test DP._mini_model(model, constraint_object(con),
        DisjunctConstraintRef[con2], mbm)== 0.0
    set_upper_bound(x, 1)
    @test DP._mini_model(model, constraint_object(con2), 
        DisjunctConstraintRef[con], mbm)== 15
    set_integer(y)
    @constraint(model, con3, y*x == 15, Disjunct(Y[1]))
    @test DP._mini_model(model, constraint_object(con2), 
        DisjunctConstraintRef[con], mbm)== 15
    JuMP.fix(y, 5; force=true)
    @test DP._mini_model(model, constraint_object(con2), 
        DisjunctConstraintRef[con], mbm)== 10
    delete_lower_bound(x)
    @test DP._mini_model(model, constraint_object(con2), 
        DisjunctConstraintRef[con2], mbm) == 1.0e9
end

function test_maximize_M()
    model = GDPModel()
    # Different bounds for x[1] and x[2] to demonstrate per-row M values
    @variable(model, x[1:2])
    set_lower_bound(x[1], 0); set_upper_bound(x[1], 10)
    set_lower_bound(x[2], 0); set_upper_bound(x[2], 5)
    @variable(model, Y[1:6], Logical)
    @constraint(model, lessthan, x[1] <= 1, Disjunct(Y[1]))
    @constraint(model, greaterthan, x[1] >= 1, Disjunct(Y[1]))
    @constraint(model, interval, 0 <= x[1] <= 55, Disjunct(Y[2]))
    @constraint(model, equalto, x[1] == 1, Disjunct(Y[3]))
    # Vector constraints: x >= 0 (both rows)
    @constraint(model, nonpositives, -x in MOI.Nonpositives(2),
        Disjunct(Y[4]))
    @constraint(model, nonnegatives, x in MOI.Nonnegatives(2),
        Disjunct(Y[5]))
    # Vector equality: x == 1 (both rows)
    @constraint(model, zeros, -x .+ 1 in MOI.Zeros(2), Disjunct(Y[6]))
    mbm = DP._MBM(DP.MBM(HiGHS.Optimizer), JuMP.Model())

    # Interval returns [M_lower, M_upper]
    # M_lower = max(0 - x[1]) s.t. 0<=x[1]<=10 = 0 at x[1]=0
    # M_upper = max(x[1] - 55) s.t. 0<=x[1]<=10 = -45 at x[1]=10, clamped to 0
    @test DP._maximize_M(model, constraint_object(interval),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]),
        mbm) == [0.0, 0.0]

    # Scalar LessThan/GreaterThan still return scalars
    # lessthan: x[1] <= 1 vs interval 0 <= x[1] <= 55
    # max(x[1] - 1) s.t. 0<=x[1]<=10 = 9 at x[1]=10
    @test DP._maximize_M(model, constraint_object(lessthan),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]),
        mbm) == 9.0

    # greaterthan: x[1] >= 1 vs interval 0 <= x[1] <= 55
    # max(1 - x[1]) s.t. 0<=x[1]<=10 = 1 at x[1]=0
    @test DP._maximize_M(model, constraint_object(greaterthan),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]),
        mbm) == 1.0

    # EqualTo returns [M_lower, M_upper]
    @test DP._maximize_M(model, constraint_object(equalto),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[3]]),
        mbm) == [0.0, 0.0]

    # Vector constraints: per-row M values
    # nonpositives: x >= 0 against Y[2] (interval only on x[1])
    # Row 1: max(0 - x[1]) s.t. 0<=x[1]<=10 = 0
    # Row 2: max(0 - x[2]) s.t. 0<=x[2]<=5 = 0
    @test DP._maximize_M(model, constraint_object(nonpositives),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]),
        mbm) == [0.0, 0.0]

    @test DP._maximize_M(model, constraint_object(nonnegatives),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]),
        mbm) == [0.0, 0.0]

    # zeros: x == 1 against Y[2] - per-row M values differ!
    # Row 1: max(|x[1] - 1|) s.t. 0<=x[1]<=10 = max(9, 1) = 9
    # Row 2: max(|x[2] - 1|) s.t. 0<=x[2]<=5 = max(4, 1) = 4
    @test DP._maximize_M(model, constraint_object(zeros),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]),
        mbm) == [9.0, 4.0]

    @test_throws ErrorException DP._maximize_M(model, "odd",
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y[2]]),
        mbm)
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
    @disjunction(model, disjunction,[Y[1], Y[2], Y[3], Y[4], Y[5]])
    bconref = Dict(Y[i] => binary_variable(Y[i]) for i in 1:5)

    # Test scalar constraints (LessThan, GreaterThan) with scalar M values
    method_scalar = DP._MBM(DP.MBM(HiGHS.Optimizer), JuMP.Model())
    for i in 1:5
        method_scalar.M[Y[i]] = Float64(i)
    end
    ref_lessthan = reformulate_disjunct_constraint(
        model, constraint_object(lessthan), bconref, method_scalar)
    ref_greaterthan = reformulate_disjunct_constraint(
        model, constraint_object(greaterthan), bconref, method_scalar)
    @test ref_lessthan[1].func == JuMP.@expression(model,
        x[1] - sum(method_scalar.M[i] * bconref[i]
            for i in keys(method_scalar.M))) &&
        ref_lessthan[1].set == MOI.LessThan(1.0)
    @test ref_greaterthan[1].func == JuMP.@expression(model,
        x[1] + sum(method_scalar.M[i] * bconref[i]
            for i in keys(method_scalar.M))) &&
        ref_greaterthan[1].set == MOI.GreaterThan(1.0)

    # Test bidirectional constraint (EqualTo) with [M_lower, M_upper] values
    method_equalto = DP._MBM(DP.MBM(HiGHS.Optimizer), JuMP.Model())
    for i in 1:5
        method_equalto.M[Y[i]] = [Float64(i), Float64(i)]
    end
    ref_equalto = reformulate_disjunct_constraint(
        model, constraint_object(equalto), bconref, method_equalto)
    @test ref_equalto[1].func == JuMP.@expression(model,
        x[1] + sum(method_equalto.M[i][1] * bconref[i]
            for i in keys(method_equalto.M))) &&
        ref_equalto[1].set == MOI.GreaterThan(1.0)
    @test ref_equalto[2].func == JuMP.@expression(model,
        x[1] - sum(method_equalto.M[i][2] * bconref[i]
            for i in keys(method_equalto.M))) &&
        ref_equalto[2].set == MOI.LessThan(1.0)

    # Test vector constraints with per-row M values [M_row1, M_row2]
    method_vector = DP._MBM(DP.MBM(HiGHS.Optimizer), JuMP.Model())
    for i in 1:5
        method_vector.M[Y[i]] = [Float64(i), Float64(i)]
    end
    ref_nonpositives = reformulate_disjunct_constraint(
        model, constraint_object(nonpositives), bconref, method_vector)
    ref_nonnegatives = reformulate_disjunct_constraint(
        model, constraint_object(nonnegatives), bconref, method_vector)
    ref_zeros = reformulate_disjunct_constraint(
        model, constraint_object(zeros), bconref, method_vector)
    @test ref_nonpositives[1].func == JuMP.@expression(model, [j=1:2],
        -x[j] - sum(method_vector.M[i][j] * bconref[i]
            for i in keys(method_vector.M))) &&
        ref_nonpositives[1].set == MOI.Nonpositives(2)
    @test ref_nonnegatives[1].func == JuMP.@expression(model, [j=1:2],
        x[j] + sum(method_vector.M[i][j] * bconref[i]
            for i in keys(method_vector.M))) &&
        ref_nonnegatives[1].set == MOI.Nonnegatives(2)
    @test ref_zeros[1].func == JuMP.@expression(model, [j=1:2],
        -x[j] + 1 + sum(method_vector.M[i][j] * bconref[i]
            for i in keys(method_vector.M))) &&
        ref_zeros[1].set == MOI.Nonnegatives(2)
    @test ref_zeros[2].func == JuMP.@expression(model, [j=1:2],
        -x[j] + 1 - sum(method_vector.M[i][j] * bconref[i]
            for i in keys(method_vector.M))) &&
        ref_zeros[2].set == MOI.Nonpositives(2)

    # Test nested disjunction reformulation with proper nested structure
    # Create outer disjunct with inner disjunction
    model2 = GDPModel()
    @variable(model2, 0 <= z <= 50)
    @variable(model2, Outer[1:2], Logical)
    @variable(model2, Inner[1:2], Logical)
    @constraint(model2, inner_lt, z <= 1, Disjunct(Inner[1]))
    @constraint(model2, inner_gt, z >= 1, Disjunct(Inner[2]))
    @disjunction(model2, inner_disj, Inner)
    method_nested = DP._MBM(DP.MBM(HiGHS.Optimizer), JuMP.Model())
    bconref2 = Dict(Outer[2] => binary_variable(Outer[2]))
    method_nested.M[Outer[2]] = 10.0 #Dummy M value for testing.
    #Normally  _reformulate_disjunct will this without having to assign a value
    ref_disjunction = reformulate_disjunct_constraint(
        model2, constraint_object(inner_disj), bconref2, method_nested)
    @test length(ref_disjunction) >= 2
    @test JuMP.coefficient(ref_disjunction[1].func, z) == 1.0
    @test JuMP.coefficient(ref_disjunction[2].func, z) == 1.0

    @test_throws ErrorException reformulate_disjunct_constraint(model,
        "odd", bconref, method_scalar)
end

function test_reformulate_disjunct()
    model = GDPModel()
    @variable(model, 1 <= x[1:2] <= 5)
    @variable(model, Y[1:2], Logical)
    @constraint(model, greaterthan, x[1] >= 1, Disjunct(Y[1]))
    @constraint(model, interval, x[1] == 2.5, Disjunct(Y[2]))

    method = DP.MBM(HiGHS.Optimizer)
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
    @test JuMP.coefficient(func_1, binary_variable(Y[2])) == 0.0

    # Per-bound M: lower bound uses M_lower=1.5, upper bound uses M_upper=2.5
    @test JuMP.coefficient(func_2, x[1]) == 1.0
    @test JuMP.coefficient(func_2, binary_variable(Y[1])) == 1.5  # M_lower

    @test JuMP.coefficient(func_3, x[1]) == 1.0
    @test JuMP.coefficient(func_3, binary_variable(Y[1])) == -2.5  # -M_upper
end

function test_reformulate_disjunction()
    model = GDPModel()
    @variable(model, x)
    @variable(model, Y[1:2], Logical)
    @constraint(model, lessthan, x <= 2, Disjunct(Y[1]))
    @constraint(model, greaterthan, x >= 1, Disjunct(Y[1]))
    @constraint(model, interval, 0 <= x <= 55, Disjunct(Y[2]))
    disj = disjunction(model, [Y[1], Y[2]])

    method = DP.MBM(HiGHS.Optimizer)
    ref_cons = reformulate_disjunction(model, constraint_object(disj), method)

    @test length(ref_cons) == 4

    @test ref_cons[1].set == MOI.LessThan(2.0)

    @test ref_cons[2].set == MOI.GreaterThan(1.0)

    @test ref_cons[3].set == MOI.GreaterThan(0.0)

    @test ref_cons[4].set == MOI.LessThan(55.0)

    # Per-constraint, per-bound M values:
    # - lessthan (x <= 2) in Y[2] region (0 <= x <= 55): max(x-2) at
    #   x=55 → M=53
    # - greaterthan (x >= 1) in Y[2] region: max(1-x) at x=0 → M=1
    # - interval in Y[1] region (1 <= x <= 2):
    #   - M_lower (x >= 0): max(0-x) at x=1 → M_lower=-1, clamped to 0
    #   - M_upper (x <= 55): max(x-55) at x=2 → M_upper=-53, clamped to 0
    func_1 = ref_cons[1].func  # x - 53*Y[2] <= 2.0
    func_2 = ref_cons[2].func  # x + 1*Y[2] >= 1.0
    func_3 = ref_cons[3].func  # x + M_lower*Y[1] >= 0.0 → x + 0*Y[1] >= 0
    func_4 = ref_cons[4].func  # x - M_upper*Y[1] <= 55 → x - 0*Y[1] <= 55

    @test JuMP.coefficient(func_1, x) == 1.0
    @test JuMP.coefficient(func_1, binary_variable(Y[2])) == -53.0

    @test JuMP.coefficient(func_2, x) == 1.0
    @test JuMP.coefficient(func_2, binary_variable(Y[2])) == 1.0

    @test JuMP.coefficient(func_3, x) == 1.0
    @test JuMP.coefficient(func_3, binary_variable(Y[1])) == 0.0

    @test JuMP.coefficient(func_4, x) == 1.0
    # -M_upper = -0 = 0
    @test JuMP.coefficient(func_4, binary_variable(Y[1])) == 0.0
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