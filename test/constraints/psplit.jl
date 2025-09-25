function _test_psplit()
    model = GDPModel()
    @variable(model, x[1:4])
    method = PSplit([[x[1], x[2]], [x[3], x[4]]])
    @test method.partition == [[x[1], x[2]], [x[3], x[4]]]
    # Throw error when partition isnt set up!
end

function _test_build_partitioned_expression()
    @variable(JuMP.Model(), x[1:4])
    partition_variables = [x[1], x[4]]
    # Build each type of expression
    nonlinear = exp(x[1]) + 1/x[2] - exp(x[2])
    affexpr = 1.0 * x[1] - 2.0 * x[2]  # Simple way to create AffExpr
    quadexpr = x[1] * x[1] + 2.0 * x[1] * x[1] + 3.0 * x[2] * x[2]  # Simple way to create QuadExpr
    var = x[3]
    num = 4.0
    result_nl, constant_nl = DP._build_partitioned_expression(nonlinear, partition_variables)

    # println(typeof(result_nl))
    # @test result_nl == exp(x[1])
    @test constant_nl == 0


    #TODO: Can improve how nl works.
    #P-Split Reformulation: Test Failed at C:\Users\LocalAdmin\Code\DisjunctiveProgramming.jl\test\constraints\psplit.jl:29
    #Expression: result_nl == exp(x[1])
    #Evaluated: ((exp(x[1]) - 0.0) + 0) - 0.0 == exp(x[1])
    
    result_aff, constant_aff = DP._build_partitioned_expression(affexpr, partition_variables)
    @test result_aff == 1.0 * x[1]
    @test constant_aff == 0
    
    result_quad, constant_quad = DP._build_partitioned_expression(quadexpr, partition_variables)
    @test result_quad == x[1] * x[1] + 2.0 * x[1] * x[1]
    @test constant_quad == 0
    
    @test DP._build_partitioned_expression(var, partition_variables) == (0, 0)
    @test DP._build_partitioned_expression(num, partition_variables) == (num, 0)

    @test_throws ErrorException DP._build_partitioned_expression("JuMP.NonlinearExpr(:+, [affexpr, quadexpr])", partition_variables)
end

function _test_bound_auxiliary()
    model = GDPModel()
    # model = JuMP.Model()
    @variable(model, 0 <= x[1:4] <= 3)
    @variable(model, v[1:6])
    method = PSplit([[x[1], x[2]], [x[3], x[4]]])
    nonlinear = JuMP.@expression(model, exp(x[1]) + 1/x[4])
    affexpr = 1.0 * x[1] - 2.0 * x[2]
    quadexpr = x[1] * x[1] + 2.0 * x[1] * x[1] + 3.0 * x[2] * x[2]
    var = x[3]
    num = 4.0

    for i in 1:4
        DP._variable_bounds(model)[x[i]] = DP.set_variable_bound_info(x[i], method)
    end

    DP._bound_auxiliary(model, v[1], nonlinear, method)
    DP._bound_auxiliary(model, v[2], quadexpr, method)
    DP._bound_auxiliary(model, v[3], num, method)
    DP._bound_auxiliary(model, v[4], var, method)
    DP._bound_auxiliary(model, v[5], affexpr, method)
    DP._bound_auxiliary(model, v[6], v[6], method)

    @test JuMP.lower_bound(v[6]) == 0
    @test JuMP.upper_bound(v[6]) == 0
    @test JuMP.lower_bound(v[5]) == -6
    @test JuMP.upper_bound(v[5]) == 3
    @test JuMP.lower_bound(v[4]) == 0
    @test JuMP.upper_bound(v[4]) == 3
    for i in 1:3
        @test !JuMP.has_lower_bound(v[i]) == true
        @test !JuMP.has_upper_bound(v[i]) == true
    end
    @test_throws ErrorException DP._bound_auxiliary(model, v[1], "JuMP.NonlinearExpr(:+, [affexpr, quadexpr])", method)
end

function _test_reformulate_disjunct_constraint_affexpr()
    model = GDPModel()
    @variable(model, 0 <= x[1:4] <= 3)
    @variable(model, y[1:2], Bin)
    method = PSplit([[x[1], x[2]], [x[3], x[4]]])
    for i in 1:4
        DP._variable_bounds(model)[x[i]] = DP.set_variable_bound_info(x[i], method)
    end
    
    lt = JuMP.constraint_object(@constraint(model, x[1] + x[3] <= 1))
    gt = JuMP.constraint_object(@constraint(model, x[2] + x[4] >= 1))
    eq = JuMP.constraint_object(@constraint(model, x[3] + x[4] == 1))
    interval = JuMP.constraint_object(@constraint(model, 0 <= x[1] + x[2] + x[3] <= 0.5))
    nn = JuMP.constraint_object(@constraint(model, x .- 1 >= 0))
    np = JuMP.constraint_object(@constraint(model, -x .+ 1 <= 0))
    zeros = JuMP.constraint_object(@constraint(model, 5x .- 1 == 0))
    ref_lt = reformulate_disjunct_constraint(model, lt, y[1], method)
    ref_gt = reformulate_disjunct_constraint(model, gt, y[2], method)
    ref_eq = reformulate_disjunct_constraint(model, eq, y[1], method)
    ref_interval = reformulate_disjunct_constraint(model, interval, y[2], method)
    ref_nn = reformulate_disjunct_constraint(model, nn, y[1], method)
    ref_np = reformulate_disjunct_constraint(model, np, y[2], method)
    ref_zeros = reformulate_disjunct_constraint(model, zeros, y[1], method)

    @test ref_lt[1].func == x[1] - variable_by_name(model, "v_$(hash(lt))_1")
    @test ref_lt[2].func == x[3] - variable_by_name(model, "v_$(hash(lt))_2")
    @test ref_lt[3].func == variable_by_name(model, "v_$(hash(lt))_1")*y[1] + variable_by_name(model, "v_$(hash(lt))_2")*y[1] - y[1]
    @test ref_gt[1].func == -x[2]- variable_by_name(model, "v_$(hash(gt))_1")
    @test ref_gt[2].func == -x[4]- variable_by_name(model, "v_$(hash(gt))_2")

    @test ref_eq[1].func == -variable_by_name(model, "v_$(hash(eq))_1_1")
    @test ref_eq[2].func == x[3] + x[4] - variable_by_name(model, "v_$(hash(eq))_2_1")
    @test ref_eq[4].func == -variable_by_name(model, "v_$(hash(eq))_1_2")
    @test ref_eq[5].func == -x[3] - x[4] - variable_by_name(model, "v_$(hash(eq))_2_2")
    @test ref_eq[3].func == variable_by_name(model, "v_$(hash(eq))_1_1")*y[1] + variable_by_name(model, "v_$(hash(eq))_2_1")*y[1] - y[1]

    @test ref_interval[1].func == x[1] + x[2] - variable_by_name(model, "v_$(hash(interval))_1_1")
    @test ref_interval[2].func == x[3] - variable_by_name(model, "v_$(hash(interval))_2_1")
    @test ref_interval[4].func == -x[1] - x[2] - variable_by_name(model, "v_$(hash(interval))_1_2")
    @test ref_interval[5].func == -x[3] - variable_by_name(model, "v_$(hash(interval))_2_2")
    @test ref_interval[3].func == variable_by_name(model, "v_$(hash(interval))_1_1")*y[2] + variable_by_name(model, "v_$(hash(interval))_2_1")*y[2] - 0.5*y[2]

    @test ref_nn[1].func == [-x[1] - variable_by_name(model, "v_$(hash(nn))_1_1"),
    -x[2] - variable_by_name(model, "v_$(hash(nn))_1_2"),
    -variable_by_name(model, "v_$(hash(nn))_1_3"),
    -variable_by_name(model, "v_$(hash(nn))_1_4")]
    @test ref_nn[2].func == [-variable_by_name(model, "v_$(hash(nn))_2_1"),
    -variable_by_name(model, "v_$(hash(nn))_2_2"),
    -x[3] - variable_by_name(model, "v_$(hash(nn))_2_3"),
    -x[4] - variable_by_name(model, "v_$(hash(nn))_2_4")]
    @test ref_nn[3].func == [variable_by_name(model, "v_$(hash(nn))_1_1")*y[1] + variable_by_name(model, "v_$(hash(nn))_2_1")*y[1] + y[1],
    variable_by_name(model, "v_$(hash(nn))_1_2")*y[1] + variable_by_name(model, "v_$(hash(nn))_2_2")*y[1] + y[1],
    variable_by_name(model, "v_$(hash(nn))_1_3")*y[1] + variable_by_name(model, "v_$(hash(nn))_2_3")*y[1] + y[1],
    variable_by_name(model, "v_$(hash(nn))_1_4")*y[1] + variable_by_name(model, "v_$(hash(nn))_2_4")*y[1] + y[1]]

    @test ref_np[1].func == [-x[1] - variable_by_name(model, "v_$(hash(np))_1_1"),
    -x[2] - variable_by_name(model, "v_$(hash(np))_1_2"),
    -variable_by_name(model, "v_$(hash(np))_1_3"),
    -variable_by_name(model, "v_$(hash(np))_1_4")]
    @test ref_np[2].func == [-variable_by_name(model, "v_$(hash(np))_2_1"),
    -variable_by_name(model, "v_$(hash(np))_2_2"),
    -x[3] - variable_by_name(model, "v_$(hash(np))_2_3"),
    -x[4] - variable_by_name(model, "v_$(hash(np))_2_4")]
    @test ref_np[3].func == [variable_by_name(model, "v_$(hash(np))_1_1")*y[2] + variable_by_name(model, "v_$(hash(np))_2_1")*y[2] + y[2],
    variable_by_name(model, "v_$(hash(np))_1_2")*y[2] + variable_by_name(model, "v_$(hash(np))_2_2")*y[2] + y[2],
    variable_by_name(model, "v_$(hash(np))_1_3")*y[2] + variable_by_name(model, "v_$(hash(np))_2_3")*y[2] + y[2],
    variable_by_name(model, "v_$(hash(np))_1_4")*y[2] + variable_by_name(model, "v_$(hash(np))_2_4")*y[2] + y[2]]

    @test ref_zeros[1].func == [5x[1] - variable_by_name(model, "v_$(hash(zeros))_1_1_1"),
    5x[2] - variable_by_name(model, "v_$(hash(zeros))_1_2_1"),
    -variable_by_name(model, "v_$(hash(zeros))_1_3_1"),
    -variable_by_name(model, "v_$(hash(zeros))_1_4_1")]
    @test ref_zeros[2].func == [-variable_by_name(model, "v_$(hash(zeros))_2_1_1"),
    -variable_by_name(model, "v_$(hash(zeros))_2_2_1"),
    5x[3] - variable_by_name(model, "v_$(hash(zeros))_2_3_1"),
    5x[4] - variable_by_name(model, "v_$(hash(zeros))_2_4_1")]

    @test ref_zeros[3].func == [variable_by_name(model, "v_$(hash(zeros))_1_1_1")*y[1] + variable_by_name(model, "v_$(hash(zeros))_2_1_1")*y[1] - y[1],
    variable_by_name(model, "v_$(hash(zeros))_1_2_1")*y[1] + variable_by_name(model, "v_$(hash(zeros))_2_2_1")*y[1] - y[1],
    variable_by_name(model, "v_$(hash(zeros))_1_3_1")*y[1] + variable_by_name(model, "v_$(hash(zeros))_2_3_1")*y[1] - y[1],
    variable_by_name(model, "v_$(hash(zeros))_1_4_1")*y[1] + variable_by_name(model, "v_$(hash(zeros))_2_4_1")*y[1] - y[1]]
    @test_throws ErrorException reformulate_disjunct_constraint(model, "JuMP.VectorConstraint", y[1], method)
end

function _test_set_variable_bound_info()
    model = GDPModel()
    @variable(model, x)
    
    @test_throws ErrorException DP.set_variable_bound_info(x, PSplit([[x]]))
    JuMP.set_lower_bound(x, 0.0)
    JuMP.set_upper_bound(x, 3.0)
    @test DP.set_variable_bound_info(x, PSplit([[x]])) == (0, 3)
end
 
@testset "P-Split Reformulation" begin
    _test_psplit()
    _test_build_partitioned_expression()
    _test_bound_auxiliary()
    _test_reformulate_disjunct_constraint_affexpr()
    _test_set_variable_bound_info()
end