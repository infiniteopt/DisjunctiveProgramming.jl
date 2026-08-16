using HiGHS

# Build a 2-disjunction GDP with known optima (8 without the global
# constraint, 6 with it)
function _basic_step_gdp(; add_global = false, optimizer = HiGHS.Optimizer)
    model = isnothing(optimizer) ? GDPModel() : GDPModel(optimizer)
    isnothing(optimizer) || set_attribute(model, MOI.Silent(), true)
    @variable(model, 0 <= x[1:2] <= 10)
    @variable(model, Y[1:2], Logical)
    @variable(model, Z[1:2], Logical)
    @objective(model, Max, x[1] + x[2])
    @constraint(model, x[1] <= 1, Disjunct(Y[1]))
    @constraint(model, 2 <= x[1] <= 3, Disjunct(Y[2]))
    @constraint(model, x[2] <= 1, Disjunct(Z[1]))
    @constraint(model, 4 <= x[2] <= 5, Disjunct(Z[2]))
    d1 = disjunction(model, Y)
    d2 = disjunction(model, Z)
    g = add_global ? @constraint(model, x[1] + x[2] <= 6) : nothing
    return model, x, Y, Z, d1, d2, g
end

function test_basic_step_creation()
    model, x, Y, Z, d1, d2, _ = _basic_step_gdp()
    orig_Y1_cons = copy(DP._indicator_to_constraints(model)[Y[1]])
    orig_obj_Y1 = constraint_object(first(orig_Y1_cons))
    new_dref = apply_basic_step(model, [d1, d2], name = "bs")
    @test new_dref isa DisjunctionRef
    @test is_valid(model, new_dref)
    @test JuMP.name(new_dref) == "bs"
    W = constraint_object(new_dref).indicators
    @test length(W) == 4
    @test JuMP.name.(W) == ["bs[1,1]", "bs[2,1]", "bs[1,2]", "bs[2,2]"]
    @test length(DP._logical_variables(model)) == 8
    for w in W
        @test length(DP._indicator_to_constraints(model)[w]) == 2
    end
    # cell (1,1) shares the constraint object of Y[1], cell (2,2) does not
    @test any(constraint_object(c) === orig_obj_Y1
              for c in DP._indicator_to_constraints(model)[W[1]])
    @test all(constraint_object(c) !== orig_obj_Y1
              for c in DP._indicator_to_constraints(model)[W[4]])
    @test haskey(DP._exactly1_constraints(model), new_dref)
    @test length(DP._exactly1_constraints(model)) == 1
    @test !is_valid(model, d1) && !is_valid(model, d2)
    @test all(!is_valid(model, c) for c in orig_Y1_cons)
    @test all(is_valid(model, lvref) for lvref in [Y..., Z...])
    # anonymous variant
    model, x, Y, Z, d1, d2, _ = _basic_step_gdp()
    new_dref = apply_basic_step(model, [d1, d2])
    @test JuMP.name(new_dref) == ""
    @test all(isempty(JuMP.name(w))
              for w in constraint_object(new_dref).indicators)
end

function test_basic_step_product_parents()
    model, x, Y, Z, d1, d2, _ = _basic_step_gdp()
    new_dref = apply_basic_step(model, [d1, d2])
    W = constraint_object(new_dref).indicators
    @test product_parents(W[1]) == [Y[1], Z[1]]
    @test product_parents(W[2]) == [Y[2], Z[1]]
    @test product_parents(W[3]) == [Y[1], Z[2]]
    @test product_parents(W[4]) == [Y[2], Z[2]]
    # original indicators are not product indicators
    @test_throws ErrorException product_parents(Y[1])
    # a repeated basic step chains through the previous products
    @variable(model, U[1:2], Logical)
    @constraint(model, x[1] >= 0, Disjunct(U[1]))
    @constraint(model, x[1] >= 1, Disjunct(U[2]))
    d3 = disjunction(model, U)
    df = apply_basic_step(model, [new_dref, d3])
    V = constraint_object(df).indicators
    @test product_parents(V[1]) == [W[1], U[1]]
    @test product_parents(product_parents(V[1])[1]) == [Y[1], Z[1]]
    # deleting a product indicator removes its mapping
    JuMP.delete(model, V[1])
    @test !haskey(DP._product_to_parents(model), V[1])
    @test_throws ErrorException product_parents(V[1])
end

function test_basic_step_linking()
    model, x, Y, Z, d1, d2, _ = _basic_step_gdp()
    new_dref = apply_basic_step(model, [d1, d2], name = "bs")
    W = constraint_object(new_dref).indicators
    # 1 product exactly1 + 4 linking constraints (originals deleted)
    @test length(DP._logical_constraints(model)) == 5
    link_data = nothing
    for (idx, data) in DP._logical_constraints(model)
        data.name == "bs_link[1,1]" && (link_data = data)
    end
    @test !isnothing(link_data)
    link_con = link_data.constraint
    @test link_con isa JuMP.VectorConstraint
    @test link_con.func == [Y[1], W[1], W[3]]
    @test link_con.set == DP._MOIExactly(3)
    # the link reformulates to w11 + w12 - y1 == 0
    reformulate_model(model, BigM())
    target = binary_variable(W[1]) + binary_variable(W[3]) -
        binary_variable(Y[1])
    @test any(
        begin
            obj = constraint_object(c)
            obj.set == MOI.EqualTo(0.0) &&
                isequal_canonical(obj.func, target)
        end for c in DP._reformulation_constraints(model))
end

function test_basic_step_globals()
    model, x, Y, Z, d1, d2, g = _basic_step_gdp(add_global = true)
    new_dref = apply_basic_step(model, [d1, d2], constraints = [g])
    for w in constraint_object(new_dref).indicators
        cons = DP._indicator_to_constraints(model)[w]
        @test length(cons) == 3
        @test any(constraint_object(c).set == MOI.LessThan(6.0)
                  for c in cons)
    end
    @test !is_valid(model, g)
end

function test_improper_basic_step()
    model, x, Y, Z, d1, d2, g = _basic_step_gdp(add_global = true)
    ret = apply_basic_step(model, [d1], constraints = [g])
    @test ret == d1
    @test is_valid(model, d1) && is_valid(model, d2)
    @test length(DP._disjunctions(model)) == 2
    @test length(DP._logical_variables(model)) == 4
    for lvref in Y
        cons = DP._indicator_to_constraints(model)[lvref]
        @test length(cons) == 2
        @test any(constraint_object(c).set == MOI.LessThan(6.0)
                  for c in cons)
    end
    # Z's disjuncts are untouched
    @test all(length(DP._indicator_to_constraints(model)[lvref]) == 1
              for lvref in Z)
    @test !is_valid(model, g)
end

# Every supported global constraint variety folds into the product
# disjuncts: EqualTo, Interval, vector Nonnegatives, quadratic, and
# nonlinear (all inactive at the optimum x = [3, 5])
function test_basic_step_global_variety()
    model, x, Y, Z, d1, d2, _ = _basic_step_gdp(optimizer = nothing)
    g_eq = @constraint(model, x[1] + x[2] == 8)
    g_int = @constraint(model, 2 <= x[1] + x[2] <= 8)
    g_vec = @constraint(model, [8 - x[1] - x[2], x[2]] in
        MOI.Nonnegatives(2))
    g_quad = @constraint(model, x[1]^2 + x[2]^2 <= 34)
    g_nl = @constraint(model, exp(x[1]) <= exp(3.0))
    globals = [g_eq, g_int, g_vec, g_quad, g_nl]
    new_dref = apply_basic_step(model, [d1, d2], constraints = globals)
    for w in constraint_object(new_dref).indicators
        cons = constraint_object.(DP._indicator_to_constraints(model)[w])
        @test length(cons) == 7
        @test any(c -> c.set == MOI.EqualTo(8.0), cons)
        @test any(c -> c.set == MOI.Interval(2.0, 8.0), cons)
        @test any(c -> c.set == MOI.Nonnegatives(2), cons)
        @test any(c -> c.func isa JuMP.GenericQuadExpr, cons)
        @test any(c -> c.func isa JuMP.GenericNonlinearExpr, cons)
    end
    @test all(!is_valid(model, g) for g in globals)
    reformulate_model(model, BigM(100))
    @test !isempty(DP._reformulation_constraints(model))
    # solve equivalence for a vector global (linear, HiGHS-solvable)
    model, x, _, _, d1, d2, _ = _basic_step_gdp()
    g_vec = @constraint(model, [6 - x[1] - x[2]] in MOI.Nonnegatives(1))
    apply_basic_step(model, [d1, d2], constraints = [g_vec])
    optimize!(model, gdp_method = BigM())
    @test objective_value(model) ≈ 6
    optimize!(model, gdp_method = Hull())
    @test objective_value(model) ≈ 6
end

function test_basic_step_large_warning()
    model = GDPModel()
    @variable(model, 0 <= x <= 100)
    @variable(model, Y[1:11], Logical)
    @variable(model, Z[1:11], Logical)
    for i in 1:11
        @constraint(model, x <= i, Disjunct(Y[i]))
        @constraint(model, x >= i, Disjunct(Z[i]))
    end
    d1 = disjunction(model, Y)
    d2 = disjunction(model, Z)
    @test_logs (:warn, r"121 product disjuncts") apply_basic_step(
        model, [d1, d2])
end

function test_basic_step_relax_products()
    model, x, Y, Z, d1, d2, _ = _basic_step_gdp()
    new_dref = apply_basic_step(model, [d1, d2], relax_products = true)
    W = constraint_object(new_dref).indicators
    for w in W
        bvref = binary_variable(w)
        @test !is_binary(bvref)
        @test lower_bound(bvref) == 0
        @test upper_bound(bvref) == 1
    end
    optimize!(model, gdp_method = BigM())
    @test termination_status(model) == MOI.OPTIMAL
    @test objective_value(model) ≈ 8
    @test all(isapprox(v, 0, atol = 1e-6) || isapprox(v, 1, atol = 1e-6)
              for v in value.(binary_variable.(W)))
    optimize!(model, gdp_method = Hull())
    @test termination_status(model) == MOI.OPTIMAL
    @test objective_value(model) ≈ 8
    # relaxed product binaries must survive the CP relax/unrelax cycle
    optimize!(model, gdp_method = CuttingPlanes(HiGHS.Optimizer))
    @test termination_status(model) == MOI.OPTIMAL
    @test objective_value(model) ≈ 8 atol = 1e-4
    @test all(!is_binary(binary_variable(w)) for w in W)
end

function test_basic_step_complement()
    model = GDPModel(HiGHS.Optimizer)
    set_attribute(model, MOI.Silent(), true)
    @variable(model, 0 <= x[1:2] <= 10)
    @variable(model, Y1, Logical)
    @variable(model, Y2, Logical, logical_complement = Y1)
    @variable(model, Z[1:2], Logical)
    @objective(model, Max, x[1] + x[2])
    @constraint(model, x[1] <= 1, Disjunct(Y1))
    @constraint(model, 2 <= x[1] <= 3, Disjunct(Y2))
    @constraint(model, x[2] <= 1, Disjunct(Z[1]))
    @constraint(model, 4 <= x[2] <= 5, Disjunct(Z[2]))
    d1 = disjunction(model, [Y1, Y2]) # complement pair, no exactly1
    d2 = disjunction(model, Z)
    new_dref = apply_basic_step(model, [d1, d2])
    @test is_valid(model, new_dref)
    @test length(constraint_object(new_dref).indicators) == 4
    optimize!(model, gdp_method = BigM())
    @test objective_value(model) ≈ 8
    optimize!(model, gdp_method = Hull())
    @test objective_value(model) ≈ 8
end

function test_basic_step_errors()
    model, x, Y, Z, d1, d2, g = _basic_step_gdp(
        add_global = true, optimizer = nothing)
    # not a GDP model
    @test_throws ErrorException apply_basic_step(Model(), [d1, d2])
    # no disjunctions
    @test_throws ErrorException apply_basic_step(model, empty([d1]))
    # single disjunction without globals
    @test_throws ErrorException apply_basic_step(model, [d1])
    # duplicate disjunctions
    @test_throws ErrorException apply_basic_step(model, [d1, d1])
    # disjunction from another model
    m2, _, _, _, d1_other, _, _ = _basic_step_gdp(optimizer = nothing)
    @test_throws ErrorException apply_basic_step(model, [d1, d1_other])
    # exactly1 = false disjunction
    @variable(model, U[1:2], Logical)
    @constraint(model, x[1] <= 5, Disjunct(U[1]))
    @constraint(model, x[1] >= 5, Disjunct(U[2]))
    d3 = disjunction(model, U, exactly1 = false)
    @test_throws ErrorException apply_basic_step(model, [d1, d3])
    # duplicate globals
    @test_throws ErrorException apply_basic_step(
        model, [d1, d2], constraints = [g, g])
    # global from another model
    m3 = GDPModel()
    @variable(m3, 0 <= t <= 1)
    g_other = @constraint(m3, t <= 0.5)
    @test_throws ErrorException apply_basic_step(
        model, [d1, d2], constraints = [g_other])
    # global with a binary variable
    @variable(model, b, Bin)
    gb = @constraint(model, x[1] + b <= 2)
    @test_throws ErrorException apply_basic_step(
        model, [d1, d2], constraints = [gb])
    # global with an unsupported set
    gs = @constraint(model, [x[1], x[2]] in SecondOrderCone())
    @test_throws ErrorException apply_basic_step(
        model, [d1, d2], constraints = [gs])
    # disjunct constraint passed as a global
    dc = first(DP._indicator_to_constraints(model)[Y[1]])
    @test_throws ErrorException apply_basic_step(
        model, [d1, d2], constraints = [dc])
    # nested disjunction inputs
    m4 = GDPModel()
    @variable(m4, 0 <= v <= 1)
    @variable(m4, A[1:2], Logical)
    @variable(m4, B[1:2], Logical)
    @variable(m4, C[1:2], Logical)
    inner = disjunction(m4, B, Disjunct(A[1]))
    outer = disjunction(m4, A)
    other = disjunction(m4, C)
    @test_throws ErrorException apply_basic_step(m4, [inner, other])
    @test_throws ErrorException apply_basic_step(m4, [outer, other])
    # indicators shared between inputs or with an outside disjunction
    m5 = GDPModel()
    @variable(m5, P[1:2], Logical)
    @variable(m5, Q[1:2], Logical)
    d5 = disjunction(m5, P)
    d6 = disjunction(m5, Q)
    d7 = disjunction(m5, [P[1], Q[2]])
    @test_throws ErrorException apply_basic_step(m5, [d5, d7])
    @test_throws ErrorException apply_basic_step(m5, [d5, d6])
    # variable bound refs and reformulation constraints as globals
    m6, x6, _, _, d8, d9, _ = _basic_step_gdp(optimizer = nothing)
    @test_throws ErrorException apply_basic_step(
        m6, [d8, d9], constraints = [UpperBoundRef(x6[1])])
    @test has_upper_bound(x6[1])
    reformulate_model(m6, BigM())
    rc = first(DP._reformulation_constraints(m6))
    @test_throws ErrorException apply_basic_step(
        m6, [d8, d9], constraints = [rc])
end

function test_basic_step_solve_equivalence()
    # proper basic step preserves the optimum
    model, _, _, _, d1, d2, _ = _basic_step_gdp()
    optimize!(model, gdp_method = BigM())
    @test objective_value(model) ≈ 8
    model, x, _, _, d1, d2, _ = _basic_step_gdp()
    apply_basic_step(model, [d1, d2])
    optimize!(model, gdp_method = BigM())
    @test termination_status(model) == MOI.OPTIMAL
    @test objective_value(model) ≈ 8
    @test value.(x) ≈ [3, 5]
    optimize!(model, gdp_method = Hull())
    @test termination_status(model) == MOI.OPTIMAL
    @test objective_value(model) ≈ 8
    @test value.(x) ≈ [3, 5]
    # intersecting the global constraint preserves the optimum
    model, _, _, _, _, _, _ = _basic_step_gdp(add_global = true)
    optimize!(model, gdp_method = BigM())
    @test objective_value(model) ≈ 6
    model, _, _, _, d1, d2, g = _basic_step_gdp(add_global = true)
    apply_basic_step(model, [d1, d2], constraints = [g])
    optimize!(model, gdp_method = BigM())
    @test objective_value(model) ≈ 6
    optimize!(model, gdp_method = Hull())
    @test objective_value(model) ≈ 6
    # improper basic step preserves the optimum
    model, _, _, _, d1, _, g = _basic_step_gdp(add_global = true)
    apply_basic_step(model, [d1], constraints = [g])
    optimize!(model, gdp_method = BigM())
    @test objective_value(model) ≈ 6
end

function test_basic_step_hull_tightness()
    function hull_bound(; basic_step)
        model = GDPModel(HiGHS.Optimizer)
        set_attribute(model, MOI.Silent(), true)
        @variable(model, 0 <= x <= 5)
        @variable(model, Y[1:2], Logical)
        @variable(model, Z[1:2], Logical)
        @objective(model, Max, x)
        @constraint(model, x <= 1, Disjunct(Y[1]))
        @constraint(model, 2 <= x <= 3, Disjunct(Y[2]))
        @constraint(model, x <= 1, Disjunct(Z[1]))
        @constraint(model, 4 <= x <= 5, Disjunct(Z[2]))
        d1 = disjunction(model, Y)
        d2 = disjunction(model, Z)
        basic_step && apply_basic_step(model, [d1, d2])
        reformulate_model(model, Hull())
        relax_integrality(model)
        optimize!(model, ignore_optimize_hook = true)
        return objective_value(model)
    end
    before = hull_bound(basic_step = false)
    after = hull_bound(basic_step = true)
    @test before ≈ 3 atol = 1e-4
    @test after ≈ 1 atol = 1e-4
    @test after <= before + 1e-6
end

function test_basic_step_repeated()
    for relax in (false, true)
        model = GDPModel(HiGHS.Optimizer)
        set_attribute(model, MOI.Silent(), true)
        @variable(model, 0 <= x[1:3] <= 10)
        @variable(model, Y[1:2], Logical)
        @variable(model, Z[1:2], Logical)
        @variable(model, U[1:2], Logical)
        @objective(model, Max, sum(x))
        @constraint(model, x[1] <= 1, Disjunct(Y[1]))
        @constraint(model, 2 <= x[1] <= 3, Disjunct(Y[2]))
        @constraint(model, x[2] <= 1, Disjunct(Z[1]))
        @constraint(model, 4 <= x[2] <= 5, Disjunct(Z[2]))
        @constraint(model, x[3] <= 2, Disjunct(U[1]))
        @constraint(model, 6 <= x[3] <= 7, Disjunct(U[2]))
        d1 = disjunction(model, Y)
        d2 = disjunction(model, Z)
        d3 = disjunction(model, U)
        dp = apply_basic_step(model, [d1, d2], relax_products = relax)
        df = apply_basic_step(model, [dp, d3], relax_products = relax)
        @test length(constraint_object(df).indicators) == 8
        @test !is_valid(model, dp)
        optimize!(model, gdp_method = BigM())
        @test termination_status(model) == MOI.OPTIMAL
        @test objective_value(model) ≈ 15
        optimize!(model, gdp_method = Hull())
        @test termination_status(model) == MOI.OPTIMAL
        @test objective_value(model) ≈ 15
    end
end

@testset "Basic Steps" begin
    test_basic_step_creation()
    test_basic_step_product_parents()
    test_basic_step_linking()
    test_basic_step_globals()
    test_basic_step_global_variety()
    test_basic_step_large_warning()
    test_improper_basic_step()
    test_basic_step_relax_products()
    test_basic_step_complement()
    test_basic_step_errors()
    test_basic_step_solve_equivalence()
    test_basic_step_hull_tightness()
    test_basic_step_repeated()
end
