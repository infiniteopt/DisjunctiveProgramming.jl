using HiGHS

function test_mbm()
    @test DP._MBM(
        DP.MBM(HiGHS.Optimizer), JuMP.Model()
    ).optimizer == HiGHS.Optimizer

    # Test _is_all_zeros
    @test DP._is_all_zeros(0)
    @test DP._is_all_zeros(0.0)
    @test !DP._is_all_zeros(1)
    @test !DP._is_all_zeros(5.0)
    @test DP._is_all_zeros([0, 0, 0])
    @test DP._is_all_zeros([0.0, 0.0])
    @test !DP._is_all_zeros([0, 1, 0])
    @test !DP._is_all_zeros([5.0, 0.0])
    @test !DP._is_all_zeros("not a number") # non-numeric fallback
end

# _var_ref_type when all map values are Numbers (no VariableRef
# found → returns V). Covers line 537.
function test__var_ref_type_numeric_map()
    model = Model()
    @variable(model, x[1:2])
    aff = @expression(model, 2*x[1] + 3*x[2])
    var_map = Dict{VariableRef, Any}(x[1] => 5.0, x[2] => 3.0)
    @test DP._var_ref_type(typeof(aff), var_map) == VariableRef
end

# replace_variables_in_constraint with QuadExpr where var_map
# maps some vars to Numbers. Covers lines 569, 571, 574.
function test__replace_variables_quad_numeric_map()
    model = Model()
    sub = Model()
    @variable(model, x[1:3])
    @variable(sub, y)
    quad1 = @expression(model, x[1] * x[2])

    # both Number (line 569)
    map1 = Dict{VariableRef, Any}(x[1] => 2.0, x[2] => 3.0)
    result1 = DP.replace_variables_in_constraint(quad1, map1)
    @test result1.aff.constant ≈ 6.0

    # ra Number, rb VariableRef (line 571)
    map2 = Dict{VariableRef, Any}(x[1] => 2.0, x[2] => y)
    result2 = DP.replace_variables_in_constraint(quad1, map2)
    @test result2.aff.terms[y] ≈ 2.0

    # rb Number, ra VariableRef (line 574)
    map3 = Dict{VariableRef, Any}(x[1] => y, x[2] => 3.0)
    result3 = DP.replace_variables_in_constraint(quad1, map3)
    @test result3.aff.terms[y] ≈ 3.0
end

function testreplace_variables_in_constraint()
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
    varref = DP.replace_variables_in_constraint(x[1], new_vars)
    expr1 = DP.replace_variables_in_constraint(
        constraint_object(con1).func, new_vars)
    expr2 = DP.replace_variables_in_constraint(
        constraint_object(con2).func, new_vars)
    expr3 = DP.replace_variables_in_constraint(
        constraint_object(con3).func, new_vars)
    expr4 = DP.replace_variables_in_constraint(
        constraint_object(con4).func, new_vars)
    @test expr1 == JuMP.@expression(sub_model, new_vars[x[1]] + 1 - 1)
    @test expr2 == JuMP.@expression(sub_model, new_vars[x[2]]*new_vars[x[1]])
    @test varref == new_vars[x[1]]
    @test expr3 isa JuMP.NonlinearExpr
    expected = JuMP.@expression(sub_model, sin(new_vars[x[3]]) - 0.0)
    @test JuMP.isequal_canonical(expr3, expected)
    @test expr4 == [new_vars[x[i]] for i in 1:3]
    @test_throws MethodError DP.replace_variables_in_constraint(
        "String", new_vars)
end

function test_prepare_max_M_objective()
    model = Model()
    sub_model = Model()

    @variable(model, x[1:2])
    @constraint(model, lessthan, x[1] <= 1)
    @constraint(model, greaterthan, x[2] >= 1)
    new_vars = Dict{VariableRef, Vector{VariableRef}}()
    for i in 1:2
        new_vars[x[i]] = [@variable(sub_model)]
    end
    sub = DP.GDPSubmodel(sub_model,
        collect(keys(new_vars)), new_vars)

    # LessThan: max(f - upper) = max(x[1] - 1)
    obj_le = DP.prepare_max_M_objective(
        model, constraint_object(lessthan), sub)
    @test obj_le == JuMP.@expression(sub_model,
        new_vars[x[1]][1] - 1)

    # GreaterThan: max(lower - f) = max(1 - x[2])
    obj_ge = DP.prepare_max_M_objective(
        model, constraint_object(greaterthan), sub)
    @test obj_ge == JuMP.@expression(sub_model,
        1 - new_vars[x[2]][1])
end

function test_raw_M()
    model = GDPModel()
    @variable(model, 0 <= x, start = 1)
    @variable(model, 0 <= y)
    @variable(model, Y[1:5], Logical)
    @constraint(model, con, 3*-x <= 4,
        Disjunct(Y[1]))
    @constraint(model, con2, 3*x + y >= 15,
        Disjunct(Y[2]))
    @constraint(model, infeasiblecon,
        3*x + y == 15, Disjunct(Y[3]))
    @constraint(model, intervalcon,
        0 <= x <= 55, Disjunct(Y[4]))
    @constraint(model, truly_infeasible,
        x >= 100, Disjunct(Y[5]))
    @disjunction(model,
        [Y[1], Y[2], Y[3], Y[4], Y[5]])
    mbm = DP._MBM(
        DP.MBM(HiGHS.Optimizer), JuMP.Model())
    sub = DP.copy_model_with_constraints(model,
        DisjunctConstraintRef[con2], mbm)
    obj = DP.prepare_max_M_objective(model,
        constraint_object(con), sub)
    @test DP.raw_M(sub, obj, mbm) == 0.0
    set_upper_bound(x, 1)
    sub2 = DP.copy_model_with_constraints(model,
        DisjunctConstraintRef[con], mbm)
    obj2 = DP.prepare_max_M_objective(model,
        constraint_object(con2), sub2)
    @test DP.raw_M(sub2, obj2, mbm) == 15
    set_integer(y)
    @constraint(model, con3, y*x == 15,
        Disjunct(Y[1]))
    obj3 = DP.prepare_max_M_objective(model,
        constraint_object(con2), sub2)
    @test DP.raw_M(sub2, obj3, mbm) == 15
    # Fresh _MBM after changing bounds
    JuMP.fix(y, 5; force=true)
    mbm2 = DP._MBM(
        DP.MBM(HiGHS.Optimizer), JuMP.Model())
    sub3 = DP.copy_model_with_constraints(model,
        DisjunctConstraintRef[con], mbm2)
    obj4 = DP.prepare_max_M_objective(model,
        constraint_object(con2), sub3)
    @test DP.raw_M(sub3, obj4, mbm2) == 10
    # Infeasible region → nothing
    delete_lower_bound(x)
    mbm3 = DP._MBM(
        DP.MBM(HiGHS.Optimizer), JuMP.Model())
    sub4 = DP.copy_model_with_constraints(model,
        DisjunctConstraintRef[con2], mbm3)
    obj5 = DP.prepare_max_M_objective(model,
        constraint_object(con2), sub4)
    @test DP.raw_M(sub4, obj5, mbm3) == nothing

    # infeasible (x >= 100 but x <= 1)
    set_upper_bound(x, 1)
    mbm4 = DP._MBM(
        DP.MBM(HiGHS.Optimizer), JuMP.Model())
    sub5 = DP.copy_model_with_constraints(model,
        DisjunctConstraintRef[truly_infeasible],
        mbm4)
    obj6 = DP.prepare_max_M_objective(model,
        constraint_object(con), sub5)
    @test DP.raw_M(sub5, obj6, mbm4) == nothing

    # Unbounded subproblem → default_M fallback.
    # No lower bound on x means max(5 - x) s.t. x <= 3
    # is unbounded (DUAL_INFEASIBLE).
    model_ub = GDPModel()
    @variable(model_ub, xu)  # no bounds
    @variable(model_ub, Yu[1:2], Logical)
    @constraint(model_ub, ub_con1, xu <= 3, Disjunct(Yu[1]))
    @constraint(model_ub, ub_con2, xu >= 5, Disjunct(Yu[2]))
    @disjunction(model_ub, [Yu[1], Yu[2]])
    mbm_ub = DP._MBM(DP.MBM(HiGHS.Optimizer), JuMP.Model())
    sub_ub = DP.copy_model_with_constraints(model_ub,
        DisjunctConstraintRef[ub_con1], mbm_ub)
    obj_ub = DP.prepare_max_M_objective(model_ub,
        constraint_object(ub_con2), sub_ub)
    @test DP.raw_M(sub_ub, obj_ub, mbm_ub) == mbm_ub.default_M
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

    # Add an infeasible disjunct (x >= 100 but bounds are 0-10)
    @variable(model, Y_infeas, Logical)
    @constraint(model, infeas_con, x[1] >= 100, Disjunct(Y_infeas))

    # Scalar constraint against infeasible disjunct -> nothing
    @test DP._maximize_M(model, constraint_object(lessthan),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y_infeas]),
        mbm) == nothing

    # Vector constraint (Nonpositives) against infeasible -> nothing
    @test DP._maximize_M(model, constraint_object(nonpositives),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y_infeas]),
        mbm) == nothing

    # Vector constraint (Nonnegatives) against infeasible -> nothing
    @test DP._maximize_M(model, constraint_object(nonnegatives),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y_infeas]),
        mbm) == nothing

    # Vector constraint (Zeros) against infeasible -> nothing
    @test DP._maximize_M(model, constraint_object(zeros),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y_infeas]),
        mbm) == nothing

    # Bidirectional scalar (EqualTo) against infeasible -> nothing
    @test DP._maximize_M(model, constraint_object(equalto),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y_infeas]),
        mbm) == nothing

    # Bidirectional scalar (Interval) against infeasible -> nothing
    @test DP._maximize_M(model, constraint_object(interval),
        Vector{DisjunctConstraintRef}(
            DP._indicator_to_constraints(model)[Y_infeas]),
        mbm) == nothing
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

    # 3 constraints: lessthan, greaterthan (with Big-M), interval (global)
    @test length(ref_cons) == 3

    @test ref_cons[1].set == MOI.LessThan(2.0)
    @test ref_cons[2].set == MOI.GreaterThan(1.0)
    # Interval is global (M=0 for both bounds in Y[1]'s region 1<=x<=2)
    @test ref_cons[3].set == MOI.Interval(0.0, 55.0)

    # Per-constraint, per-bound M values:
    # - lessthan (x <= 2) in Y[2] region (0 <= x <= 55): max(x-2) at
    #   x=55 -> M=53
    # - greaterthan (x >= 1) in Y[2] region: max(1-x) at x=0 -> M=1
    # - interval in Y[1] region (1 <= x <= 2):
    #   - M_lower (x >= 0): max(0-x) at x=1 -> M_lower=-1, clamped to 0
    #   - M_upper (x <= 55): max(x-55) at x=2 -> M_upper=-53, clamped to 0
    #   - Both M=0 -> detected as global, added without Big-M
    func_1 = ref_cons[1].func  # x - 53*Y[2] <= 2.0
    func_2 = ref_cons[2].func  # x + 1*Y[2] >= 1.0
    func_3 = ref_cons[3].func  # x (global, no binary variables)

    @test JuMP.coefficient(func_1, x) == 1.0
    @test JuMP.coefficient(func_1, binary_variable(Y[2])) == -53.0

    @test JuMP.coefficient(func_2, x) == 1.0
    @test JuMP.coefficient(func_2, binary_variable(Y[2])) == 1.0

    # Global constraint has just x, no binary variables
    @test JuMP.coefficient(func_3, x) == 1.0

    # Test infeasible disjunct throws error
    model2 = GDPModel()
    @variable(model2, 0 <= z <= 1)
    @variable(model2, W[1:2], Logical)
    # W[1]: z >= 5 is infeasible (z has upper bound 1)
    @constraint(model2, z >= 5, Disjunct(W[1]))
    # W[2]: z <= 0.5 is feasible
    @constraint(model2, z <= 0.5, Disjunct(W[2]))
    disj2 = disjunction(model2, [W[1], W[2]])

    method2 = DP.MBM(HiGHS.Optimizer)
    @test_throws ErrorException reformulate_disjunction(
        model2, constraint_object(disj2), method2)

    model4 = GDPModel()
    @variable(model4, 0 <= u <= 10)
    @variable(model4, U[1:2], Logical)
    @constraint(model4, u <= 3, Disjunct(U[1]))
    @constraint(model4, u >= 5, Disjunct(U[2]))
    disj4 = disjunction(model4, [U[1], U[2]])

    method4 = DP.MBM(HiGHS.Optimizer)
    ref_cons4 = @test_nowarn begin
        reformulate_disjunction(model4, constraint_object(disj4), method4)
    end
    @test length(ref_cons4) == 2

    # Disjunct 1: x <= 10 (will be global because D2's region has x <= 5)
    # Disjunct 2: x <= 5
    # max(x - 10) s.t. x <= 5 = 5 - 10 = -5, clamped to 0
    # So M = 0 for D1's constraint -> it's global
    model5 = GDPModel()
    @variable(model5, 0 <= g <= 10)
    @variable(model5, G[1:2], Logical)
    @constraint(model5, g <= 10, Disjunct(G[1]))  # global: other region is g<=5
    @constraint(model5, g <= 5, Disjunct(G[2]))
    disj5 = disjunction(model5, [G[1], G[2]])

    method5 = DP.MBM(HiGHS.Optimizer)
    ref_cons5 = reformulate_disjunction(model5, constraint_object(disj5), method5)
    # G[1]'s constraint is global (added without Big-M)
    # G[2]'s constraint has M > 0 (needs Big-M): max(g - 5) s.t. g<=10 = 5
    @test length(ref_cons5) == 2
    # Check that one constraint has binary variable coefficient (Big-M term)
    # and one doesn't (global)
    global_con = ref_cons5[1]  # g <= 10 (global)
    bigm_con = ref_cons5[2]    # g <= 5 with Big-M
    @test global_con.set == MOI.LessThan(10.0)
    @test bigm_con.set == MOI.LessThan(5.0)
    # Global constraint should have no binary variable coefficient
    @test JuMP.coefficient(global_con.func, binary_variable(G[2])) == 0.0
    # Big-M constraint should have binary variable coefficient = -5
    @test JuMP.coefficient(bigm_con.func, binary_variable(G[1])) == -5.0
end

################################################################################
#                    LOW-LEVEL UNIT TESTS FOR MBM INFRASTRUCTURE
################################################################################

# Test _copy_model directly
function test__copy_model()
    # Test with standard JuMP Model
    model = Model()
    @variable(model, x >= 0)
    @variable(model, y <= 10)
    copied = DP._copy_model(model)
    @test copied isa Model
    @test num_variables(copied) == 0  # _copy_model creates empty model

    # Test with GDPModel
    gdp_model = GDPModel()
    @variable(gdp_model, z)
    copied_gdp = DP._copy_model(gdp_model)
    @test copied_gdp isa Model
    @test num_variables(copied_gdp) == 0
end

# Test VariableProperties struct and constructors
function test_variable_properties()
    # Test VariableProperties(vref::GenericVariableRef) - standard JuMP variable
    model = GDPModel()
    @variable(model, 0 <= x <= 10, start = 5)
    props_x = DP.VariableProperties(x)
    @test props_x.info.has_lb == true
    @test props_x.info.lower_bound == 0
    @test props_x.info.has_ub == true
    @test props_x.info.upper_bound == 10
    @test props_x.info.has_start == true
    @test props_x.info.start == 5
    @test props_x.name == "x"
    @test props_x.variable_type === nothing

    # Test with binary variable
    @variable(model, y, Bin)
    props_y = DP.VariableProperties(y)
    @test props_y.info.binary == true
    @test props_y.info.integer == false

    # Test with integer variable
    @variable(model, z, Int)
    props_z = DP.VariableProperties(z)
    @test props_z.info.binary == false
    @test props_z.info.integer == true

    # Test with fixed variable
    @variable(model, w == 42)
    props_w = DP.VariableProperties(w)
    @test props_w.info.has_fix == true
    @test props_w.info.fixed_value == 42

    # Test VariableProperties(expr) - blank info constructor
    expr = 2*x + 3*y
    props_expr = DP.VariableProperties(expr)
    @test props_expr.info.has_lb == false
    @test props_expr.info.has_ub == false
    @test props_expr.info.has_fix == false
    @test props_expr.info.has_start == false
    @test props_expr.info.binary == false
    @test props_expr.info.integer == false
    @test props_expr.name == ""
end

# Test _make_variable_object
function test__make_variable_object()
    model = GDPModel()
    @variable(model, 0 <= x <= 10, start = 5)

    # Create VariableProperties and then make variable object
    props = DP.VariableProperties(x)
    var_obj = DP._make_variable_object(props)
    @test var_obj isa JuMP.ScalarVariable
    @test var_obj.info.has_lb == true
    @test var_obj.info.lower_bound == 0
    @test var_obj.info.has_ub == true
    @test var_obj.info.upper_bound == 10

    # Test with blank properties (from expression)
    props_blank = DP.VariableProperties(2*x)
    var_obj_blank = DP._make_variable_object(props_blank)
    @test var_obj_blank isa JuMP.ScalarVariable
    @test var_obj_blank.info.has_lb == false
    @test var_obj_blank.info.has_ub == false
end

# Test create_variable
function test_create_variable()
    model = GDPModel()
    @variable(model, 0 <= x <= 10, start = 5)

    # Create a new variable from properties
    props = DP.VariableProperties(x)
    new_var = DP.create_variable(model, props)
    @test new_var isa VariableRef
    @test has_lower_bound(new_var)
    @test lower_bound(new_var) == 0
    @test has_upper_bound(new_var)
    @test upper_bound(new_var) == 10
    @test start_value(new_var) == 5
    @test name(new_var) == "x"

    # Test with binary variable
    @variable(model, y, Bin)
    props_bin = DP.VariableProperties(y)
    new_bin = DP.create_variable(model, props_bin)
    @test is_binary(new_bin)

    # Test with integer variable
    @variable(model, z, Int)
    props_int = DP.VariableProperties(z)
    new_int = DP.create_variable(model, props_int)
    @test is_integer(new_int)

    # Test with fixed variable
    @variable(model, w == 42)
    props_fix = DP.VariableProperties(w)
    new_fix = DP.create_variable(model, props_fix)
    @test is_fixed(new_fix)
    @test fix_value(new_fix) == 42
end

# Test variable_copy
function test_variable_copy()
    source_model = GDPModel()
    @variable(source_model, 0 <= x <= 10, start = 5)
    @variable(source_model, y, Bin)
    @variable(source_model, z, Int)
    @variable(source_model, w == 42)

    target_model = GDPModel()

    # Copy bounded variable
    x_copy = DP.variable_copy(target_model, x)
    @test x_copy isa VariableRef
    @test owner_model(x_copy) === target_model
    @test has_lower_bound(x_copy)
    @test lower_bound(x_copy) == 0
    @test has_upper_bound(x_copy)
    @test upper_bound(x_copy) == 10
    @test start_value(x_copy) == 5
    @test name(x_copy) == "x"

    # Copy binary variable
    y_copy = DP.variable_copy(target_model, y)
    @test is_binary(y_copy)
    @test owner_model(y_copy) === target_model

    # Copy integer variable
    z_copy = DP.variable_copy(target_model, z)
    @test is_integer(z_copy)
    @test owner_model(z_copy) === target_model

    # Copy fixed variable
    w_copy = DP.variable_copy(target_model, w)
    @test is_fixed(w_copy)
    @test fix_value(w_copy) == 42
    @test owner_model(w_copy) === target_model
end

# Test _copy_model_with_constraints (combines _copy_model + variable_copy + constraint handling)
function test__copy_model_with_constraints()
    model = GDPModel()
    @variable(model, 0 <= x <= 10)
    @variable(model, 0 <= y <= 5)
    @variable(model, Y[1:2], Logical)
    @constraint(model, con1, x + y <= 8, Disjunct(Y[1]))
    @constraint(model, con2, x - y >= 2, Disjunct(Y[2]))
    @disjunction(model, [Y[1], Y[2]])

    mbm = DP._MBM(DP.MBM(HiGHS.Optimizer), JuMP.Model())
    constraints = Vector{DisjunctConstraintRef}(
        DP._indicator_to_constraints(model)[Y[1]]
    )

    sub = DP.copy_model_with_constraints(model, constraints, mbm)

    # Check submodel struct
    @test sub isa DP.GDPSubmodel
    @test sub.model isa Model
    # Check variable mapping exists
    @test haskey(sub.fwd_map, x)
    @test haskey(sub.fwd_map, y)

    # Check mapped variables (length-1 vectors)
    @test length(sub.fwd_map[x]) == 1
    @test length(sub.fwd_map[y]) == 1

    # Check bounds in submodel
    xm = sub.fwd_map[x][1]
    ym = sub.fwd_map[y][1]
    @test has_lower_bound(xm)
    @test lower_bound(xm) == 0
    @test has_upper_bound(xm)
    @test upper_bound(xm) == 10

    @test has_lower_bound(ym)
    @test lower_bound(ym) == 0
    @test has_upper_bound(ym)
    @test upper_bound(ym) == 5

    # Check constraint was added to submodel
    @test num_constraints(sub.model, AffExpr,
        MOI.LessThan{Float64}) == 1
end

# Test get_variable_info
function test_get_variable_info()
    model = GDPModel()
    @variable(model, 0 <= x <= 10, start = 5)
    @variable(model, y, Bin)
    @variable(model, z == 42)

    # Test bounded variable
    info_x = DP.get_variable_info(x)
    @test info_x.has_lb == true
    @test info_x.lower_bound == 0
    @test info_x.has_ub == true
    @test info_x.upper_bound == 10
    @test info_x.has_start == true
    @test info_x.start == 5
    @test info_x.binary == false
    @test info_x.integer == false

    # Test binary variable
    info_y = DP.get_variable_info(y)
    @test info_y.binary == true
    @test info_y.integer == false

    # Test fixed variable
    info_z = DP.get_variable_info(z)
    @test info_z.has_fix == true
    @test info_z.fixed_value == 42

    # Test with overridden kwargs
    info_custom = DP.get_variable_info(x; has_lb = false, has_ub = false)
    @test info_custom.has_lb == false
    @test info_custom.has_ub == false
end

@testset "MBM" begin
    test__copy_model()
    test_variable_properties()
    test__make_variable_object()
    test_create_variable()
    test_variable_copy()
    test__copy_model_with_constraints()
    test_get_variable_info()
    test_mbm()
    test__var_ref_type_numeric_map()
    test__replace_variables_quad_numeric_map()
    testreplace_variables_in_constraint()
    test_prepare_max_M_objective()
    test_raw_M()
    test_maximize_M()
    test_reformulate_disjunct_constraint()
    test_reformulate_disjunct()
    test_reformulate_disjunction()
end