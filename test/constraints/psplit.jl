function test_psplit()
    model = GDPModel()
    @variable(model, x[1:4])
    method = PSplit([[x[1], x[2]], [x[3], x[4]]])
    @test method.partition == [[x[1], x[2]], [x[3], x[4]]]
end

function test_build_partitioned_expression()
    model = JuMP.Model()
    @variable(model, x[1:4])
    partition_variables = [x[1], x[4]]
    
    test_cases = [
        (expr = 1.0 * x[1] - 2.0 * x[2], expected = (1.0 * x[1], 0.0)),
        (expr = x[1] * x[1] + 2.0 * x[1] * x[1] + 3.0 * x[2] * x[2], 
        expected = (3 * x[1] * x[1], 0.0)),
        (expr = x[3], expected = (0, 0)),
        (expr = x[4], expected = (x[4], 0.0)),
        (expr = 4.0, expected = (4.0, 0.0))
    ]

    for (i, test_case) in enumerate(test_cases)
        result = DP._build_partitioned_expression(test_case.expr, partition_variables)
        @test result == test_case.expected
    end

    @test_throws ErrorException DP._build_partitioned_expression(
        "Bad Input", 
        partition_variables
    )
end

function test_bound_auxiliary()
    model = GDPModel()
    @variable(model, 0 <= x[1:4] <= 3)
    @variable(model, v[1:6])
    method = PSplit([[x[1], x[2]], [x[3], x[4]]])
    affexpr = 1.0 * x[1] - 2.0 * x[2]
    quadexpr = x[1] * x[1] + 2.0 * x[1] * x[1] - 3.0 * x[2] * x[2] + x[1] - x[2]
    var = x[3]
    num = 4.0
    nl = exp(x[1])
    for i in 1:4
        DP._variable_bounds(model)[x[i]] = DP.set_variable_bound_info(x[i], method)
    end

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
    @test JuMP.lower_bound(v[2]) == -30
    @test JuMP.upper_bound(v[2]) == 30

    @test has_lower_bound(v[3]) == false
    @test has_upper_bound(v[3]) == false
    @test_throws ErrorException DP._bound_auxiliary(model, v[3], nl, method)
end

function test_reformulate_disjunct_constraint_affexpr()
    model = GDPModel()
    @variable(model, 0 <= x[1:4] <= 3)
    @variable(model, y[1:2], Bin)
    method = PSplit([[x[1], x[2]], [x[3], x[4]]])
    for i in 1:4
        DP._variable_bounds(model)[x[i]] = DP.set_variable_bound_info(
            x[i], 
            method
        )
    end

    lt = JuMP.constraint_object(@constraint(model, x[1] + x[3] <= 1))
    gt = JuMP.constraint_object(@constraint(model, x[2] + x[4] >= 1))
    eq = JuMP.constraint_object(@constraint(model, x[3] + x[4] == 1))
    interval = JuMP.constraint_object(
        @constraint(model, 0 <= x[1] + x[2] + x[3] <= 0.5)
    )
    nn = JuMP.constraint_object(@constraint(model, x .- 1 >= 0))
    np = JuMP.constraint_object(@constraint(model, -x .+ 1 <= 0))
    zeros = JuMP.constraint_object(@constraint(model, 5x .- 1 == 0))
    
    ref_lt = reformulate_disjunct_constraint(model, lt, y[1], method)
    ref_gt = reformulate_disjunct_constraint(model, gt, y[2], method)
    ref_eq = reformulate_disjunct_constraint(model, eq, y[1], method)
    ref_interval = reformulate_disjunct_constraint(
        model, interval, y[2], method
    )
    ref_nn = reformulate_disjunct_constraint(model, nn, y[1], method)
    ref_np = reformulate_disjunct_constraint(model, np, y[2], method)
    ref_zeros = reformulate_disjunct_constraint(model, zeros, y[1], method)

    @test ref_lt[1].func == x[1] - 
        variable_by_name(model, "v_$(hash(lt))_1")
    @test ref_lt[2].func == x[3] - 
        variable_by_name(model, "v_$(hash(lt))_2")
    @test ref_lt[3].func == 
        variable_by_name(model, "v_$(hash(lt))_1") * y[1] + 
        variable_by_name(model, "v_$(hash(lt))_2") * y[1] - 
        y[1]
    @test ref_gt[1].func == -x[2] - 
        variable_by_name(model, "v_$(hash(gt))_1")
    @test ref_gt[2].func == -x[4] - 
        variable_by_name(model, "v_$(hash(gt))_2")

    @test ref_eq[1].func == 
        -variable_by_name(model, "v_$(hash(eq))_1_1")
    @test ref_eq[2].func == x[3] + x[4] - 
        variable_by_name(model, "v_$(hash(eq))_2_1")
    @test ref_eq[4].func == 
        -variable_by_name(model, "v_$(hash(eq))_1_2")
    @test ref_eq[5].func == -x[3] - x[4] - 
        variable_by_name(model, "v_$(hash(eq))_2_2")
    @test ref_eq[3].func == 
        variable_by_name(model, "v_$(hash(eq))_1_1") * y[1] + 
        variable_by_name(model, "v_$(hash(eq))_2_1") * y[1] - 
        y[1]

    @test ref_interval[1].func == x[1] + x[2] - 
        variable_by_name(model, "v_$(hash(interval))_1_1")
    @test ref_interval[2].func == x[3] - 
        variable_by_name(model, "v_$(hash(interval))_2_1")
    @test ref_interval[4].func == -x[1] - x[2] - 
        variable_by_name(model, "v_$(hash(interval))_1_2")
    @test ref_interval[5].func == -x[3] - 
        variable_by_name(model, "v_$(hash(interval))_2_2")
    @test ref_interval[3].func == 
        variable_by_name(model, "v_$(hash(interval))_1_1") * y[2] + 
        variable_by_name(model, "v_$(hash(interval))_2_1") * y[2] - 
        0.5 * y[2]

    @test ref_nn[1].func == [
        -x[1] - variable_by_name(model, "v_$(hash(nn))_1_1"),
        -x[2] - variable_by_name(model, "v_$(hash(nn))_1_2"),
        -variable_by_name(model, "v_$(hash(nn))_1_3"),
        -variable_by_name(model, "v_$(hash(nn))_1_4")
    ]

    @test ref_nn[2].func == [
        -variable_by_name(model, "v_$(hash(nn))_2_1"),
        -variable_by_name(model, "v_$(hash(nn))_2_2"),
        -x[3] - variable_by_name(model, "v_$(hash(nn))_2_3"),
        -x[4] - variable_by_name(model, "v_$(hash(nn))_2_4")
    ]

    @test ref_nn[3].func == [
        variable_by_name(model, "v_$(hash(nn))_1_1") * y[1] + 
        variable_by_name(model, "v_$(hash(nn))_2_1") * y[1] + y[1],
        variable_by_name(model, "v_$(hash(nn))_1_2") * y[1] + 
        variable_by_name(model, "v_$(hash(nn))_2_2") * y[1] + y[1],
        variable_by_name(model, "v_$(hash(nn))_1_3") * y[1] + 
        variable_by_name(model, "v_$(hash(nn))_2_3") * y[1] + y[1],
        variable_by_name(model, "v_$(hash(nn))_1_4") * y[1] + 
        variable_by_name(model, "v_$(hash(nn))_2_4") * y[1] + y[1]
    ]

    @test ref_np[1].func == [
        -x[1] - variable_by_name(model, "v_$(hash(np))_1_1"),
        -x[2] - variable_by_name(model, "v_$(hash(np))_1_2"),
        -variable_by_name(model, "v_$(hash(np))_1_3"),
        -variable_by_name(model, "v_$(hash(np))_1_4")
    ]

    @test ref_np[2].func == [
        -variable_by_name(model, "v_$(hash(np))_2_1"),
        -variable_by_name(model, "v_$(hash(np))_2_2"),
        -x[3] - variable_by_name(model, "v_$(hash(np))_2_3"),
        -x[4] - variable_by_name(model, "v_$(hash(np))_2_4")
    ]

    @test ref_np[3].func == [
        variable_by_name(model, "v_$(hash(np))_1_1") * y[2] + 
        variable_by_name(model, "v_$(hash(np))_2_1") * y[2] + y[2],
        variable_by_name(model, "v_$(hash(np))_1_2") * y[2] + 
        variable_by_name(model, "v_$(hash(np))_2_2") * y[2] + y[2],
        variable_by_name(model, "v_$(hash(np))_1_3") * y[2] + 
        variable_by_name(model, "v_$(hash(np))_2_3") * y[2] + y[2],
        variable_by_name(model, "v_$(hash(np))_1_4") * y[2] + 
        variable_by_name(model, "v_$(hash(np))_2_4") * y[2] + y[2]
    ]

    @test ref_zeros[1].func == [
        5x[1] - variable_by_name(model, "v_$(hash(zeros))_1_1_1"),
        5x[2] - variable_by_name(model, "v_$(hash(zeros))_1_2_1"),
        -variable_by_name(model, "v_$(hash(zeros))_1_3_1"),
        -variable_by_name(model, "v_$(hash(zeros))_1_4_1")
    ]

    @test ref_zeros[2].func == [
        -variable_by_name(model, "v_$(hash(zeros))_2_1_1"),
        -variable_by_name(model, "v_$(hash(zeros))_2_2_1"),
        5x[3] - variable_by_name(model, "v_$(hash(zeros))_2_3_1"),
        5x[4] - variable_by_name(model, "v_$(hash(zeros))_2_4_1")
    ]
end

function test_reformulate_disjunct()
    model = GDPModel()
    @variable(model, 0 <= x[1:4] <= 1)
    @variable(model, Y[1:2], Logical)
    @variable(model, W[1:2], Logical)
    @disjunction(model, [Y[1], Y[2]])
    @disjunction(model, [W[1], W[2]])
    method = PSplit([[x[1], x[2]], [x[3], x[4]]])
    for i in 1:4
        DP._variable_bounds(model)[x[i]] = DP.set_variable_bound_info(x[i], method)
    end
    ref_cons1 = Vector{JuMP.AbstractConstraint}()
    ref_cons2 = Vector{JuMP.AbstractConstraint}()
    
    good_quad = @constraint(model, x[1]^2 + x[2]^2 <= 1, Disjunct(W[2]))
    good_quad2 = @constraint(model, x[3]^2 + x[4]^2 <= 1, Disjunct(W[2]))
    affexpr = @constraint(model, x[1] + x[2] <= 1, Disjunct(W[1]))
    nonlinear_con = @constraint(model, exp(x[1]) <= 1, Disjunct(Y[1]))
    bad_quad = @constraint(model, x[1]*x[2] <= 1, Disjunct(Y[2]))

    @test_throws ErrorException DP._reformulate_disjunct(model, ref_cons1, Y[2], method)
    @test_throws ErrorException DP._reformulate_disjunct(model, ref_cons2, Y[1], method)
    
    DP._reformulate_disjunct(model, ref_cons1, W[2], method)
    DP._reformulate_disjunct(model, ref_cons2, W[1], method)

    @test length(ref_cons1) == 6
    @test length(ref_cons2) == 3
end



function test_set_variable_bound_info()
    model = GDPModel()
    @variable(model, x)
    
    @test_throws ErrorException DP.set_variable_bound_info(x, PSplit([[x]]))
    JuMP.set_lower_bound(x, 0.0)
    JuMP.set_upper_bound(x, 3.0)
    @test DP.set_variable_bound_info(x, PSplit([[x]])) == (0, 3)
end
 
@testset "P-Split Reformulation" begin
    test_psplit()
    test_build_partitioned_expression()
    test_set_variable_bound_info()
    test_bound_auxiliary()
    test_reformulate_disjunct_constraint_affexpr()
    test_reformulate_disjunct()
end