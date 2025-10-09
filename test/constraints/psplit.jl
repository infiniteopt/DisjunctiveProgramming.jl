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

    @test JuMP.upper_bound(v[3]) == 4
    @test JuMP.lower_bound(v[3]) == 4
    @test_throws ErrorException DP._bound_auxiliary(model, v[3], nl, method)
end


# function test_reformulate_disjunct()
#     model = GDPModel()
#     @variable(model, 0 <= x[1:4] <= 1)
#     @variable(model, Y[1:2], Logical)
#     @variable(model, W[1:2], Logical)
#     @disjunction(model, [Y[1], Y[2]])
#     @disjunction(model, [W[1], W[2]])
#     method = PSplit([[x[1], x[2]], [x[3], x[4]]])
#     for i in 1:4
#         DP._variable_bounds(model)[x[i]] = DP.set_variable_bound_info(x[i], method)
#     end
#     ref_cons1 = Vector{JuMP.AbstractConstraint}()
#     ref_cons2 = Vector{JuMP.AbstractConstraint}()
    
#     good_quad = @constraint(model, x[1]^2 + x[2]^2 <= 1, Disjunct(W[2]))
#     good_quad2 = @constraint(model, x[3]^2 + x[4]^2 <= 1, Disjunct(W[2]))
#     affexpr = @constraint(model, x[1] + x[2] <= 1, Disjunct(W[1]))
#     nonlinear_con = @constraint(model, exp(x[1]) <= 1, Disjunct(Y[1]))
#     bad_quad = @constraint(model, x[1]*x[2] <= 1, Disjunct(Y[2]))

#     @test_throws ErrorException DP._reformulate_disjunct(model, ref_cons1, Y[2], method)
#     @test_throws ErrorException DP._reformulate_disjunct(model, ref_cons2, Y[1], method)
    
#     DP._reformulate_disjunct(model, ref_cons1, W[2], method)
#     DP._reformulate_disjunct(model, ref_cons2, W[1], method)

#     @test length(ref_cons1) == 6
#     @test length(ref_cons2) == 3
# end



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
end