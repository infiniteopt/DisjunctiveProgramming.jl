function test_psplit()
    model = JuMP.Model()
    @variable(model, x[1:4])
    method = PSplit([[x[1], x[2]], [x[3], x[4]]])
    @test method.partition == [[x[1], x[2]], [x[3], x[4]]]
    #Throw error when partition isnt set up!
end
#=
TODO: Test Plan

_build_partitioned_expression: 5 tests
contains_only_partition_variables: 5 tests (2 for union + 3 others)
_nonlinear_recursion: 5 tests (4 for union + 1 other)
_bound_auxiliary: 6 tests (3 for union + 3 others)
reformulate_disjunct_constraint: 8 tests (2 for Interval/EqualTo + 3 for vector sets + 3 others)
Utility functions: 2 tests
=#

@testset "P-Split Reformulation" begin
    test_psplit()
end