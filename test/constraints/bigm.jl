function test_default_bigm()
    method = BigM()
    @test method.value == 1e9
    @test method.tighten
end

function test_default_tighten_bigm()
    method = BigM(100)
    @test method.value == 100
    @test method.tighten
end

function test_set_bigm()
    method = BigM(1e6, false)
    @test method.value == 1e6
    @test !method.tighten
end

function test_get_M_1sided()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y, Logical)
    @constraint(model, con, 3*x <= 1, Disjunct(y))
    cobj = constraint_object(con)
    @test DP._get_M(cobj.func, cobj.set, BigM(100, false)) == 100
    @test_throws ErrorException DP._get_M(cobj.func, cobj.set, BigM(Inf, false))
end

function test_get_tight_M_1sided()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y, Logical)
    @constraint(model, con, 3*x <= 1, Disjunct(y))
    cobj = constraint_object(con)

    method = BigM(100)
    @test prep_bounds(x, model, method) isa Nothing
    @test DP._get_tight_M(cobj.func, cobj.set, method) == 100
    clear_bounds(model)

    method = BigM(Inf)
    prep_bounds(x, model, method)
    @test_throws ErrorException DP._get_tight_M(cobj.func, cobj.set, method)
    clear_bounds(model)

    set_upper_bound(x, 10)
    method = BigM()
    prep_bounds(x, model, method)
    @test DP._get_tight_M(cobj.func, cobj.set, method) == 29
    clear_bounds(model)
end

function test_get_M_2sided()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y, Logical)
    @constraint(model, con, 3*x == 1, Disjunct(y))
    cobj = constraint_object(con)

    method = BigM(100)
    @test DP._get_M(cobj.func, cobj.set, method) == [100., 100.]

    method = BigM(Inf)
    @test_throws ErrorException DP._get_M(cobj.func, cobj.set, method)
end

function test_get_tight_M_2sided()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y, Logical)
    @constraint(model, con, 3*x == 1, Disjunct(y))
    cobj = constraint_object(con)
    
    method = BigM(100)
    prep_bounds(x, model, method)
    @test DP._get_tight_M(cobj.func, cobj.set, method) == (100., 100.)
    clear_bounds(model)

    method = BigM(Inf)
    prep_bounds(x, model, method)
    @test_throws ErrorException DP._get_tight_M(cobj.func, cobj.set, method)
    clear_bounds(model)

    set_lower_bound(x, -10)
    set_upper_bound(x, 10)
    method = BigM()
    prep_bounds(x, model, method)
    @test DP._get_tight_M(cobj.func, cobj.set, method) == (31., 29.)
    clear_bounds(model)
end

function test_interval_arithmetic_LessThan()
    model = GDPModel()
    @variable(model, x[1:3])
    @variable(model, y, Bin)
    @expression(model, func, -x[1] + 2*x[2] - 3*x[3] + 4*y + 5)

    method = BigM()
    prep_bounds(x, model, method)
    @test isinf(DP._interval_arithmetic_LessThan(func, 0.0, method))
    clear_bounds(model)

    set_upper_bound.(x, 10)
    method = BigM()
    prep_bounds(x, model, method)
    @test isinf(DP._interval_arithmetic_LessThan(func, 0.0, method))
    clear_bounds(model)

    set_lower_bound.(x, -10)
    method = BigM()
    prep_bounds(x, model, method)
    M = -(-10) + 2*10 - 3*(-10) + 5 
    @test DP._interval_arithmetic_LessThan(func, 0.0, method) == M
    clear_bounds(model)
end

function test_interval_arithmetic_GreaterThan()
    model = GDPModel()
    @variable(model, x[1:3])
    @variable(model, y, Bin)
    @expression(model, func, -x[1] + 2*x[2] - 3*x[3] + 4*y + 5)

    method = BigM()
    prep_bounds(x, model, method)
    @test isinf(DP._interval_arithmetic_GreaterThan(func, 0.0, method))
    clear_bounds(model)

    set_upper_bound.(x, 10)
    method = BigM()
    prep_bounds(x, model, method)
    @test isinf(DP._interval_arithmetic_GreaterThan(func, 0.0, method))
    clear_bounds(model)

    set_lower_bound.(x, -10)
    method = BigM()
    prep_bounds(x, model, method)
    expected = -(10) + 2*(-10) - 3*(10) + 5 
    @test DP._interval_arithmetic_GreaterThan(func, 0.0, method) == -expected
    clear_bounds(model)
end

function test_calculate_tight_M()
    model = GDPModel()
    @variable(model, -1 <= x <= 1)
    method = BigM()
    prep_bounds(x, model, method)
    @test DP._calculate_tight_M(1*x, MOI.LessThan(5.0), method) == -4
    @test DP._calculate_tight_M(1*x, MOI.GreaterThan(5.0), method) == 6
    @test DP._calculate_tight_M(1*x, MOI.Nonpositives(3), method) == 1
    @test DP._calculate_tight_M(1*x, MOI.Nonnegatives(3), method) == 1
    @test DP._calculate_tight_M(1*x, MOI.Interval(5.0, 5.0), method) == (6., -4.)
    @test DP._calculate_tight_M(1*x, MOI.EqualTo(5.0), method) == (6., -4.)
    @test DP._calculate_tight_M(1*x, MOI.Zeros(3), method) == (1., 1.)
    for ex in (x^2, exp(x)), set in (MOI.LessThan(5.0), MOI.GreaterThan(5.0), MOI.Nonpositives(4), MOI.Nonnegatives(4))
        @test isinf(DP._calculate_tight_M(ex, set, method))
    end
    for ex in (x^2, exp(x)), set in (MOI.Interval(5.0,5.0), MOI.EqualTo(5.0), MOI.Zeros(4))
        @test all(isinf.(DP._calculate_tight_M(ex, set, method)))
    end
    @test_throws ErrorException DP._calculate_tight_M(1*x, MOI.SOS1([1.0,3.0,2.5]), method)
end

function test_lessthan_bigm()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y, Logical)
    @constraint(model, con, x <= 5, Disjunct(y))

    bvref = binary_variable(y)
    ref = reformulate_disjunct_constraint(model, constraint_object(con), bvref, BigM(100, false))
    @test length(ref) == 1
    @test ref[1].func == x - 100*(-bvref)
    @test ref[1].set == MOI.LessThan(5.0 + 100)
end

function test_nonpositives_bigm()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y, Logical)
    @constraint(model, con, [x; x] <= [5; 5], Disjunct(y))

    bvref = binary_variable(y)
    ref = reformulate_disjunct_constraint(model, constraint_object(con), bvref, BigM(100, false))
    @test length(ref) == 1
    @test ref[1].func[1] == x - 5 - 100*(1-bvref)
    @test ref[1].func[2] == x - 5 - 100*(1-bvref)
    @test ref[1].set == MOI.Nonpositives(2)
end

function test_greaterthan_bigm()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y, Logical)
    @constraint(model, con, x >= 5, Disjunct(y))

    bvref = binary_variable(y)
    ref = reformulate_disjunct_constraint(model, constraint_object(con), bvref, BigM(100, false))
    @test length(ref) == 1
    @test ref[1].func == x + 100*(-bvref)
    @test ref[1].set == MOI.GreaterThan(5.0 - 100)
end

function test_nonnegatives_bigm()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y, Logical)
    @constraint(model, con, [x; x] >= [5; 5], Disjunct(y))

    bvref = binary_variable(y)
    ref = reformulate_disjunct_constraint(model, constraint_object(con), bvref, BigM(100, false))
    @test length(ref) == 1
    @test ref[1].func[1] == x - 5 + 100*(1-bvref)
    @test ref[1].func[2] == x - 5 + 100*(1-bvref)
    @test ref[1].set == MOI.Nonnegatives(2)
end

function test_equalto_bigm()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y, Logical)
    @constraint(model, con, x == 5, Disjunct(y))

    bvref = binary_variable(y)
    ref = reformulate_disjunct_constraint(model, constraint_object(con), bvref, BigM(100, false))
    @test length(ref) == 2
    @test ref[1].func == x + 100*(-bvref)
    @test ref[1].set == MOI.GreaterThan(5.0 - 100)
    @test ref[2].func == x - 100*(-bvref)
    @test ref[2].set == MOI.LessThan(5.0 + 100)
end

function test_interval_bigm()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y, Logical)
    @constraint(model, con, 5 <= x <= 5, Disjunct(y))

    bvref = binary_variable(y)
    ref = reformulate_disjunct_constraint(model, constraint_object(con), bvref, BigM(100, false))
    @test length(ref) == 2
    @test ref[1].func == x + 100*(-bvref)
    @test ref[1].set == MOI.GreaterThan(5.0 - 100)
    @test ref[2].func == x - 100*(-bvref)
    @test ref[2].set == MOI.LessThan(5.0 + 100)
end

function test_zeros_bigm()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y, Logical)
    @constraint(model, con, [x; x] == [5; 5], Disjunct(y))

    bvref = binary_variable(y)
    ref = reformulate_disjunct_constraint(model, constraint_object(con), bvref, BigM(100, false))
    @test length(ref) == 2
    @test ref[1].func[1] == x - 5 + 100*(1-bvref)
    @test ref[1].func[2] == x - 5 + 100*(1-bvref)
    @test ref[1].set == MOI.Nonnegatives(2)
    @test ref[2].func[1] == x - 5 - 100*(1-bvref)
    @test ref[2].func[2] == x - 5 - 100*(1-bvref)
    @test ref[2].set == MOI.Nonpositives(2)
end

function test_nested_bigm()
    model = GDPModel()
    @variable(model, -100 <= x <= 100)
    @variable(model, y[1:2], Logical)
    @variable(model, z[1:2], Logical)
    @constraint(model, x <= 5, Disjunct(y[1]))
    @constraint(model, x >= 5, Disjunct(y[2]))
    @disjunction(model, inner, y, Disjunct(z[1]), exactly1 = false)
    @constraint(model, x <= 10, Disjunct(z[1]))
    @constraint(model, x >= 10, Disjunct(z[2]))
    @disjunction(model, outer, z, exactly1 = false)

    reformulate_model(model, BigM())
    bvrefs = DP._indicator_to_binary(model)
    refcons = constraint_object.(DP._reformulation_constraints(model))
    @test length(refcons) == 4
    @test refcons[1].func == x - 95*(-bvrefs[y[1]])
    @test refcons[1].set == MOI.LessThan(5.0 + 95)
    @test refcons[2].func == x + 105*(-bvrefs[y[2]])
    @test refcons[2].set == MOI.GreaterThan(5.0 - 105)
    @test refcons[3].func == x - 90*(-bvrefs[z[1]])
    @test refcons[3].set == MOI.LessThan(10.0 + 90)
    @test refcons[4].func == x + 110*(-bvrefs[z[2]])
    @test refcons[4].set == MOI.GreaterThan(10.0 - 110)
end

function test_extension_bigm()
    model = GDPModel{MyModel, MyVarRef, MyConRef}()
    @variable(model, -100 <= x <= 100)
    @variable(model, y[1:2], Logical(MyVar))
    @variable(model, z[1:2], Logical(MyVar))
    @constraint(model, x <= 5, Disjunct(y[1]))
    @constraint(model, x >= 5, Disjunct(y[2]))
    @disjunction(model, inner, y, Disjunct(z[1]), exactly1 = false)
    @constraint(model, x <= 10, Disjunct(z[1]))
    @constraint(model, x >= 10, Disjunct(z[2]))
    @disjunction(model, outer, z, exactly1 = false)

    @test reformulate_model(model, BigM()) isa Nothing
    bvrefs = DP._indicator_to_binary(model)
    refcons = constraint_object.(DP._reformulation_constraints(model))
    @test length(refcons) == 4
    @test refcons[1].func == x - 95*(-bvrefs[y[1]])
    @test refcons[1].set == MOI.LessThan(5.0 + 95)
    @test refcons[2].func == x + 105*(-bvrefs[y[2]])
    @test refcons[2].set == MOI.GreaterThan(5.0 - 105)
    @test refcons[3].func == x - 90*(-bvrefs[z[1]])
    @test refcons[3].set == MOI.LessThan(10.0 + 90)
    @test refcons[4].func == x + 110*(-bvrefs[z[2]])
    @test refcons[4].set == MOI.GreaterThan(10.0 - 110)
end

function test_soc_bigm()
    model = GDPModel()
    @variable(model, x)
    @variable(model, t)
    @variable(model, y, Logical)
    @constraint(model, con, [t, x] in SecondOrderCone(), Disjunct(y))
    bvref = binary_variable(y)
    ref = reformulate_disjunct_constraint(model, constraint_object(con), bvref, BigM(100, false))
    @test length(ref) == 1
    @test isequal_canonical(ref[1].func[1], t + 100*(1 - bvref))
    @test isequal_canonical(ref[1].func[2], 1.0*x)
    @test ref[1].set == MOI.SecondOrderCone(2)
end

function test_rsoc_bigm()
    model = GDPModel()
    @variable(model, x)
    @variable(model, t)
    @variable(model, y, Logical)
    @constraint(model, con, [0.5, t, x] in RotatedSecondOrderCone(), Disjunct(y))
    bvref = binary_variable(y)
    ref = reformulate_disjunct_constraint(model, constraint_object(con), bvref, BigM(100, false))
    @test length(ref) == 1
    @test isequal_canonical(ref[1].func[1], 0.5 + 100*(1 - bvref))
    @test isequal_canonical(ref[1].func[2], t + 100*(1 - bvref))
    @test isequal_canonical(ref[1].func[3], 1.0*x)
    @test ref[1].set == MOI.RotatedSecondOrderCone(3)
end

function test_exp_bigm()
    model = GDPModel()
    @variable(model, x)
    @variable(model, t)
    @variable(model, w)
    @variable(model, y, Logical)
    @constraint(model, con, [x, t, w] in MOI.ExponentialCone(), Disjunct(y))
    bvref = binary_variable(y)
    ref = reformulate_disjunct_constraint(model, constraint_object(con), bvref, BigM(100, false))
    @test length(ref) == 1
    @test isequal_canonical(ref[1].func[1], 1.0*x)
    @test isequal_canonical(ref[1].func[2], t + 100*(1 - bvref))
    @test isequal_canonical(ref[1].func[3], w + 200*(1 - bvref))
    @test ref[1].set == MOI.ExponentialCone()
end

function test_power_bigm()
    model = GDPModel()
    @variable(model, x)
    @variable(model, t)
    @variable(model, w)
    @variable(model, y, Logical)
    @constraint(model, con, [x, t, w] in MOI.PowerCone(0.5), Disjunct(y))
    bvref = binary_variable(y)
    ref = reformulate_disjunct_constraint(model, constraint_object(con), bvref, BigM(100, false))
    @test length(ref) == 1
    @test isequal_canonical(ref[1].func[1], x + 100*(1 - bvref))
    @test isequal_canonical(ref[1].func[2], t + 100*(1 - bvref))
    @test isequal_canonical(ref[1].func[3], 1.0*w)
    @test ref[1].set == MOI.PowerCone(0.5)
end

@testset "BigM Reformulation" begin
    test_default_bigm()
    test_default_tighten_bigm()
    test_set_bigm()
    test_get_M_1sided()
    test_get_tight_M_1sided()
    test_get_M_2sided()
    test_get_tight_M_2sided()
    test_interval_arithmetic_LessThan()
    test_interval_arithmetic_GreaterThan()
    test_calculate_tight_M()
    test_lessthan_bigm()
    test_nonpositives_bigm()
    test_greaterthan_bigm()
    test_nonnegatives_bigm()
    test_equalto_bigm()
    test_interval_bigm()
    test_zeros_bigm()
    test_nested_bigm()
    test_extension_bigm()
    test_soc_bigm()
    test_rsoc_bigm()
    test_exp_bigm()
    test_power_bigm()
end