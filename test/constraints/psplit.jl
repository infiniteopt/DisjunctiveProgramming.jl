function test_psplit()
    model = JuMP.Model()
    @variable(model, x[1:4])
    method = PSplit([[x[1], x[2]], [x[3], x[4]]])
    @test method.partition == [[x[1], x[2]], [x[3], x[4]]]
    #Throw error when partition isnt set up!
end
#=
TODO: Test Plan

_build_partitioned_expression: 6 tests (DONE)
contains_only_partition_variables: 5 tests (2 for union + 3 others)
_nonlinear_recursion: 5 tests (4 for union + 1 other)
_bound_auxiliary: 6 tests (3 for union + 3 others)
reformulate_disjunct_constraint: 8 tests (2 for Interval/EqualTo + 3 for vector sets + 3 others)
Utility functions: 2 tests
=#

function test_build_partitioned_expression()
    model = JuMP.Model()
    @variable(model, x[1:4])
    partition_variables = [x[1], x[4]]
    # Build each type of expression
    nonlinear = exp(x[1])
    affexpr = 1.0 * x[1] - 2.0 * x[2]  # Simple way to create AffExpr
    quadexpr = x[1] * x[1] + 2.0 * x[1] * x[1] + 3.0 * x[2] * x[2]  # Simple way to create QuadExpr
    var = x[3]
    num = 4.0
    
    con = JuMP.build_constraint(error, nonlinear, MOI.EqualTo(0.0))
    result_nl, rhs_nl = DP._build_partitioned_expression(nonlinear, partition_variables, con)
    #Why can't I test with an equivalent expression?
    #Example output
    #P-Split Reformulation: Test Failed at c:\Users\LocalAdmin\Code\DisjunctiveProgramming.jl\test\constraints\psplit.jl:33
    #Expression: result_nl == NonlinearExpr(:exp, Any[x[1]])
    #Evaluated: exp(x[1]) == exp(x[1])


    println(typeof(result_nl))
    # @test JuMP.value(result_nl, 1) == exp(x[1])
    @test rhs_nl == 0
    
    result_aff, rhs_aff = DP._build_partitioned_expression(affexpr, partition_variables, nothing)
    @test result_aff == 1.0 * x[1]
    @test rhs_aff == 0
    
    result_quad, rhs_quad = DP._build_partitioned_expression(quadexpr, partition_variables, nothing)
    @test result_quad == x[1] * x[1] + 2.0 * x[1] * x[1]
    @test rhs_quad == 0
    
    @test DP._build_partitioned_expression(var, partition_variables, nothing) == (0, 0)
    @test DP._build_partitioned_expression(num, partition_variables, nothing) == (num, 0)

    @test_throws ErrorException DP._build_partitioned_expression(JuMP.NonlinearExpr(:+, [affexpr, quadexpr]), partition_variables, nothing)
end

function _test_contains_only_partition_variables()
    #TODO: GenericAffExpr, GenericQuadExpr, GenericNonlinearExpr, VariableRef, Number, ErrorException
end

@testset "P-Split Reformulation" begin
    test_psplit()
    test_build_partitioned_expression()
end