using HiGHS

function test_linear_gdp_example(m, use_complements = false)
    set_attribute(m, MOI.Silent(), true)
    @variable(m, 1 ≤ x[1:2] ≤ 9)
    if use_complements
        @variable(m, Y1, Logical)
        @variable(m, Y2, Logical, logical_complement = Y1)
        Y = [Y1, Y2]
    else
        @variable(m, Y[1:2], Logical)
    end
    @variable(m, W[1:2], Logical)
    @objective(m, Max, sum(x))
    @constraint(m, y1[i=1:2], [1,4][i] ≤ x[i] ≤ [3,6][i], Disjunct(Y[1]))
    @constraint(m, w1[i=1:2], [1,5][i] ≤ x[i] ≤ [2,6][i], Disjunct(W[1]))
    @constraint(m, w2[i=1:2], [2,4][i] ≤ x[i] ≤ [3,5][i], Disjunct(W[2]))
    @constraint(m, y2[i=1:2], [8,1][i] ≤ x[i] ≤ [9,2][i], Disjunct(Y[2]))
    @disjunction(m, inner, [W[1], W[2]], Disjunct(Y[1]))
    @disjunction(m, outer, [Y[1], Y[2]])

    @test optimize!(m, gdp_method = BigM()) isa Nothing
    @test termination_status(m) == MOI.OPTIMAL
    @test objective_value(m) ≈ 11
    @test value.(x) ≈ [9,2]
    @test !value(Y[1])
    @test value(Y[2])
    @test !value(W[1])
    @test !value(W[2])
    @test optimize!(m, gdp_method = Hull()) isa Nothing
    @test termination_status(m) == MOI.OPTIMAL
    @test objective_value(m) ≈ 11
    @test value.(x) ≈ [9,2]
    @test !value(Y[1])
    @test value(Y[2])
    @test !value(W[1])
    @test !value(W[2])
    @test value(variable_by_name(m, "x[1]_W[1]")) ≈ 0
    @test value(variable_by_name(m, "x[1]_W[2]")) ≈ 0
    @test value(variable_by_name(m, "x[2]_W[1]")) ≈ 0
    @test value(variable_by_name(m, "x[2]_W[2]")) ≈ 0
    if !use_complements
        @test value(variable_by_name(m, "x[1]_Y[1]")) ≈ 0
        @test value(variable_by_name(m, "x[1]_Y[2]")) ≈ 9
        @test value(variable_by_name(m, "x[2]_Y[1]")) ≈ 0
        @test value(variable_by_name(m, "x[2]_Y[2]")) ≈ 2
    end

    @test optimize!(m, gdp_method = MBM(HiGHS.Optimizer)) isa Nothing
    @test termination_status(m) == MOI.OPTIMAL
    @test objective_value(m) ≈ 11
    @test value.(x) ≈ [9,2]
    @test !value(Y[1])
    @test value(Y[2])
    @test !value(W[1])
    @test !value(W[2])

end

function test_generic_model(m)
    set_attribute(m, MOI.Silent(), true)
    @variable(m, 1 ≤ x[1:2] ≤ 9)
    @variable(m, Y[1:2], Logical)
    @variable(m, W[1:2], Logical)
    @objective(m, Max, sum(x))
    @constraint(m, y1[i=1:2], [1,4][i] ≤ x[i] ≤ [3,6][i], Disjunct(Y[1]))
    @constraint(m, w1[i=1:2], [1,5][i] ≤ x[i] ≤ [2,6][i], Disjunct(W[1]))
    @constraint(m, w2[i=1:2], [2,4][i] ≤ x[i] ≤ [3,5][i], Disjunct(W[2]))
    @constraint(m, y2[i=1:2], [8,1][i] ≤ x[i] ≤ [9,2][i], Disjunct(Y[2]))
    @disjunction(m, inner, [W[1], W[2]], Disjunct(Y[1]))
    @disjunction(m, outer, [Y[1], Y[2]])

    @test optimize!(m, gdp_method = BigM()) isa Nothing
    @test optimize!(m, gdp_method = Hull()) isa Nothing
    @test optimize!(m, gdp_method = Indicator()) isa Nothing

    # TODO add meaningful tests to check the constraints/variables
end

@testset "Solve Linear GDP" begin
    test_linear_gdp_example(GDPModel(HiGHS.Optimizer))
    test_linear_gdp_example(GDPModel(HiGHS.Optimizer), true)
    mockoptimizer = () -> MOI.Utilities.MockOptimizer(
        MOI.Utilities.UniversalFallback(MOIU.Model{Float32}()),
        eval_objective_value = false
        )
    test_generic_model(GDPModel{Float32}(mockoptimizer))
end