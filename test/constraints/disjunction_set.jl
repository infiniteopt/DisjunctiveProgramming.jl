using HiGHS

# Two disjuncts on x: [x <= 2] ∨ [x >= 8]
const _RAISE_SETS = [[MOI.LessThan(2.0)], [MOI.GreaterThan(8.0)]]

_raised_disjunctions(model) = DisjunctionRef.(model,
    keys(DP._disjunctions(model)))

function test_raise_two_binaries()
    model = GDPModel()
    @variable(model, 0 <= x <= 10)
    @variable(model, y[1:2], Bin)
    @constraint(model, d, [1, y[1], y[2], x, x] in DisjunctionSet(_RAISE_SETS))
    num_vars = num_variables(model)
    reformulate_model(model, BigM())
    @test isempty(all_constraints(model, Vector{AffExpr}, DisjunctionSet))
    dref = only(_raised_disjunctions(model))
    @test name(dref) == "d"
    indicators = constraint_object(dref).indicators
    @test binary_variable.(indicators) == y
    @test name.(indicators) == name.(y)
    @test num_variables(model) == num_vars
    sets = [constraint_object(only(DP._indicator_to_constraints(model)[lv])).set
        for lv in indicators]
    @test sets == [MOI.LessThan(2.0), MOI.GreaterThan(8.0)]
end

function test_raise_complement()
    model = GDPModel()
    @variable(model, 0 <= x <= 10)
    @variable(model, y, Bin)
    @constraint(model, [1, y, 1 - y, x, x] in DisjunctionSet(_RAISE_SETS))
    num_vars = num_variables(model)
    reformulate_model(model, Hull())
    indicators = constraint_object(only(_raised_disjunctions(model))).indicators
    @test binary_variable(indicators[1]) == y
    @test has_logical_complement(indicators[2])
    @test binary_variable(indicators[2]) == 1 - y
    @test length(DP._logical_variables(model)) == 2
end

function test_raise_nested()
    model = GDPModel()
    @variable(model, 0 <= x <= 10)
    @variable(model, y[1:2], Bin)
    @variable(model, w[1:2], Bin)
    inner_sets = [[MOI.LessThan(1.0)], [MOI.GreaterThan(1.5)]]
    # child listed first: raising must not depend on order
    @constraint(model, [y[1], w[1], w[2], x, x] in DisjunctionSet(inner_sets))
    @constraint(model, [1, y[1], y[2], x, x] in DisjunctionSet(_RAISE_SETS))
    reformulate_model(model, BigM())
    drefs = _raised_disjunctions(model)
    @test length(drefs) == 2
    nested = filter(dref -> constraint_object(dref).nested, drefs)
    @test binary_variable.(constraint_object(only(nested)).indicators) == w
    parent = DP._indicator_to_binary(model)
    parent_lvref = only(lv for (lv, b) in parent if b == y[1])
    @test any(cref -> constraint_object(cref) isa Disjunction,
        DP._indicator_to_constraints(model)[parent_lvref])
end

function test_raise_quadratic()
    # one quadratic row makes every entry, indicators included, a QuadExpr
    model = GDPModel()
    @variable(model, 0 <= x <= 10)
    @variable(model, y[1:2], Bin)
    @constraint(model, [1, y[1], y[2], x^2, x] in DisjunctionSet(_RAISE_SETS))
    reformulate_model(model, BigM(100, false))
    indicators = constraint_object(only(_raised_disjunctions(model))).indicators
    @test binary_variable.(indicators) == y
end

function test_raise_errors()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:3], Bin)
    @constraint(model, [1, 2y[1], y[2], x, x] in DisjunctionSet(_RAISE_SETS))
    @test_throws ErrorException reformulate_model(model, BigM())

    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2], Bin)
    sets = [[MOI.LessThan(1.0)], [MOI.LessThan(2.0)], [MOI.LessThan(3.0)]]
    @constraint(model, [1, y[1], 1 - y[1], y[2], x, x, x] in
        DisjunctionSet(sets))
    @test_throws ErrorException reformulate_model(model, BigM())

    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:3], Bin)
    @constraint(model, [y[3], y[1], y[2], x, x] in DisjunctionSet(_RAISE_SETS))
    @test_throws ErrorException reformulate_model(model, BigM())

    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2])
    @constraint(model, [1, y[1], y[2], x, x] in DisjunctionSet(_RAISE_SETS))
    @test_throws ErrorException reformulate_model(model, BigM())

    for indicator in (y -> y^2, sin)
        model = GDPModel()
        @variable(model, x)
        @variable(model, y[1:2], Bin)
        @constraint(model, [1, indicator(y[1]), y[2], x, x] in
            DisjunctionSet(_RAISE_SETS))
        @test_throws ErrorException reformulate_model(model, BigM())
    end
end

# The receiver path: an MOI model holding `DisjunctionSet` is copied into a
# `GDPModel`, raised, and solved with existing reformulations.
function test_raise_from_moi_copy()
    for method in (BigM(), Hull(), MBM(HiGHS.Optimizer), Indicator())
        method isa Indicator && continue  # HiGHS has no indicator support
        source = Model()
        @variable(source, 0 <= x <= 9)
        @variable(source, y, Bin)
        @objective(source, Max, x)
        @constraint(source, [1, y, 1 - y, x, x] in DisjunctionSet(_RAISE_SETS))
        model = GDPModel()
        MOI.copy_to(backend(model), backend(source))
        set_optimizer(model, HiGHS.Optimizer)
        set_silent(model)
        optimize!(model, gdp_method = method)
        @test termination_status(model) == MOI.OPTIMAL
        @test objective_value(model) ≈ 9 atol = 1e-6
    end
end

@testset "DisjunctionSet raising" begin
    test_raise_two_binaries()
    test_raise_complement()
    test_raise_nested()
    test_raise_quadratic()
    test_raise_errors()
    test_raise_from_moi_copy()
end
