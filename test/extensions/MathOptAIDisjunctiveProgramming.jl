using HiGHS, MathOptAI
import DisjunctiveProgramming as DP

# x[1] <= 0 ? -1 : (x[1] <= 1 ? 0 : 1), MathOptAI's own docstring example.
# The atol gap sits well above HiGHS's MIP feasibility tolerance (1e-6).
_step_tree(atol = 1e-3) = MathOptAI.BinaryDecisionTree{Float64, Int}(1, 0.0,
    -1, MathOptAI.BinaryDecisionTree{Float64, Int}(1, 1.0, 0, 1, atol), atol)

# linear model tree: x[1] <= 1 ? 2 x[1] - x[2] : x[1] + 3 x[2] + 1
const _AffineTree = MathOptAI.BinaryDecisionTree{Float64,
    MathOptAI.Affine{Float64}}
_affine_tree(atol = 1e-3) = _AffineTree(1, 1.0,
    MathOptAI.Affine([2.0 -1.0], [0.0]),
    MathOptAI.Affine([1.0 3.0], [1.0]), atol)
_affine_truth(x) = x[1] < 1 ? 2x[1] - x[2] : x[1] + 3x[2] + 1

# surrogate value at pinned inputs, from the GDP embedding or MathOptAI's own
# MIP; the pin is a global equality so the box the M values are read from
# stays [lb, ub] and every leaf keeps a feasible region
function _surrogate_value(model, predictor, xval, lb, ub; kwargs...)
    set_silent(model)
    @variable(model, lb[i] <= x[i in eachindex(xval)] <= ub[i])
    y, _ = MathOptAI.add_predictor(model, predictor, x)
    @constraint(model, x .== xval)
    optimize!(model; kwargs...)
    return is_solved_and_feasible(model) ? value(y[1]) : nothing
end
_gdp_value(predictor, method, xval, lb, ub) = _surrogate_value(
    GDPModel(HiGHS.Optimizer), Disjunctive(predictor), xval, lb, ub,
    gdp_method = method)
_moai_value(predictor, xval, lb, ub) =
    _surrogate_value(Model(HiGHS.Optimizer), predictor, xval, lb, ub)

function test_disjunctive_wrapper()
    predictor = Disjunctive(_step_tree())
    @test predictor isa MathOptAI.AbstractPredictor
    @test predictor.predictor isa MathOptAI.BinaryDecisionTree
end

function test_tree_formulation_contents()
    model = GDPModel(HiGHS.Optimizer)
    set_silent(model)
    @variable(model, -5 <= x[1:1] <= 5)
    y, formulation = MathOptAI.add_predictor(model, Disjunctive(_step_tree()),
        x)
    @test length(y) == 1
    @test lower_bound(y[1]) == -1 && upper_bound(y[1]) == 1
    @test formulation isa MathOptAI.Formulation
    @test formulation.predictor isa typeof(Disjunctive(_step_tree()))
    # the output and the three leaf indicators
    @test length(formulation.variables) == 1 + 3
    @test formulation.variables[1] === y[1]
    @test all(v -> v isa LogicalVariableRef, formulation.variables[2:end])
    # two output bounds, 5 path rows, 3 leaf rows and the disjunction
    @test length(formulation.constraints) == 2 + 5 + 3 + 1
    @test all(c -> is_valid(model, c), formulation.constraints)
    dref = formulation.constraints[end]
    @test dref isa DisjunctionRef
    @test length(DP._disjunctions(model)) == 1
    @test length(DP._disjunct_constraints(model)) == 5 + 3
    @test haskey(DP._exactly1_constraints(model), dref)
    # the GDP method is chosen at solve time like for any disjunction
    @objective(model, Max, y[1] - 0.1 * x[1])
    optimize!(model, gdp_method = BigM())
    @test is_solved_and_feasible(model)
    @test value(y[1]) ≈ 1 && value(x[1]) ≈ 1
    @objective(model, Min, y[1] + 0.1 * x[1])
    optimize!(model, gdp_method = Hull())
    @test value(y[1]) ≈ -1 && value(x[1]) ≈ -5
end

# every method reproduces MathOptAI's leaf regions, including the atol gap
function test_tree_matches_mathoptai()
    methods = [BigM(), Hull(), MBM(HiGHS.Optimizer), Indicator()]
    for xval in [-2.0, -0.01, 0.0, 0.5, 0.99, 1.0, 3.0]
        expected = _moai_value(_step_tree(), [xval], [-5], [5])
        @test expected !== nothing
        for method in methods
            @test _gdp_value(_step_tree(), method, [xval], [-5], [5]) ≈
                expected atol = 1e-8
        end
    end
    @test _moai_value(_step_tree(), [1 - 5e-4], [-5], [5]) === nothing
    for method in methods
        @test _gdp_value(_step_tree(), method, [1 - 5e-4], [-5], [5]) ===
            nothing
    end
end

# whole-model methods apply too, since nothing is reformulated early
function test_cutting_planes()
    model = GDPModel(HiGHS.Optimizer)
    set_silent(model)
    @variable(model, -5 <= x[1:1] <= 5)
    y, _ = MathOptAI.add_predictor(model, Disjunctive(_step_tree()), x)
    @objective(model, Max, y[1] - 0.1 * x[1])
    optimize!(model, gdp_method = CuttingPlanes(HiGHS.Optimizer))
    @test is_solved_and_feasible(model)
    @test value(y[1]) ≈ 1 atol = 1e-4
    @test value(x[1]) ≈ 1 atol = 1e-4
end

function test_affine_leaves()
    for method in [BigM(), Hull()], xval in
        [[-2.0, 0.5], [0.0, 0.0], [0.999, -1.0], [1.0, 2.0], [3.0, 1.5]]
        @test _gdp_value(_affine_tree(), method, xval, [-3, -3], [3, 3]) ≈
            _affine_truth(xval) atol = 1e-6
    end
    # envelope bounds and a free optimum
    model = GDPModel(HiGHS.Optimizer)
    set_silent(model)
    @variable(model, -3 <= x[1:2] <= 3)
    y, formulation = MathOptAI.add_predictor(model,
        Disjunctive(_affine_tree()), x)
    @test lower_bound(y[1]) == -11 && upper_bound(y[1]) == 13
    @objective(model, Max, y[1])
    optimize!(model, gdp_method = Hull())
    @test is_solved_and_feasible(model)
    @test value(y[1]) ≈ 13 && value(x[1]) ≈ 3 && value(x[2]) ≈ 3
    @objective(model, Min, y[1])
    optimize!(model, gdp_method = Hull())
    @test value(y[1]) ≈ -9 && value(x[1]) ≈ -3 && value(x[2]) ≈ 3
end

@testset "MathOptAIDisjunctiveProgramming" begin
    test_disjunctive_wrapper()
    test_tree_formulation_contents()
    test_tree_matches_mathoptai()
    test_cutting_planes()
    test_affine_leaves()
end
