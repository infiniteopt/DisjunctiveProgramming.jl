using InfiniteOpt, HiGHS

function test_infiniteopt_extension()
    # Initialize the model
    model = InfiniteGDPModel(HiGHS.Optimizer)

    # Create the infinite variables
    I = 1:4
    @infinite_parameter(model, t ∈ [0, 1], num_supports = 100)
    @variable(model, 0 <= g[I] <= 10, Infinite(t))

    # Add the disjunctions and their indicator variables
    @variable(model, G[I, 1:2], InfiniteLogical(t))
    @test all(isa.(@constraint(model, [i ∈ I, j ∈ 1:2], 0 <= g[i], Disjunct(G[i, 1])), DisjunctConstraintRef{InfiniteModel}))
    @test all(isa.(@constraint(model, [i ∈ I, j ∈ 1:2], g[i] <= 0, Disjunct(G[i, 2])), DisjunctConstraintRef{InfiniteModel}))
    @test all(isa.(@disjunction(model, [i ∈ I], G[i, :]), DisjunctionRef{InfiniteModel}))

    # Add the logical propositions
    @variable(model, W, InfiniteLogical(t))
    @test @constraint(model, G[1, 1] ∨ G[2, 1] ∧ G[3, 1] == W := true) isa LogicalConstraintRef{InfiniteModel}
    @constraint(model, 𝔼(binary_variable(W), t) >= 0.95)

    # Reformulate and solve 
    @test optimize!(model, gdp_method = Hull()) isa Nothing

    # check the results
    @test all(value(W))
end

@testset "InfiniteDisjunctiveProgramming" begin
    test_infiniteopt_extension()
end