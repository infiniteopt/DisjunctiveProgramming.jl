function test_default_hull()
    @test Hull().value == 1e-6
end

function test_set_hull()
    @test Hull(0.001).value == 0.001
end

function test_query_variable_bounds()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, -100 <= y <= -10)
    prep_bounds([x, y], model, Hull())
    @test variable_bound_info(x) == (0, 100)
    @test variable_bound_info(y) == (-100, 0)
end

function test_query_variable_bounds_error1()
    model = GDPModel()
    @variable(model, x <= 100)
    @test_throws ErrorException set_variable_bound_info(x, Hull())
end

function test_query_variable_bounds_error2()
    model = GDPModel()
    @variable(model, -100 <= x)
    @test_throws ErrorException set_variable_bound_info(x, Hull())
end

function test_disaggregate_variables()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, y, Bin)
    @variable(model, z, Logical)
    vrefs = Set([x,y])
    @test prep_bounds(x, model, Hull()) isa Nothing
    method = DP._Hull(Hull(1e-3), vrefs)
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing
    @test haskey(method.disjunct_variables, (x, DP._indicator_to_binary(model)[z]))

    refvars = DP._reformulation_variables(model)
    @test length(refvars) == 1
    zbin = variable_by_name(model, "z")
    @test zbin == binary_variable(z)
    x_z = variable_by_name(model, "x_z")
    @test x_z in refvars
    @test has_lower_bound(x_z) && lower_bound(x_z) == 0
    @test has_upper_bound(x_z) && upper_bound(x_z) == 100
    @test name(x_z) == "x_z"
    x_z_lb = constraint_by_name(model, "x_z_lower_bound") |> constraint_object
    @test x_z_lb.func == -x_z
    @test x_z_lb.set == MOI.LessThan(0.)
    x_z_ub = constraint_by_name(model, "x_z_upper_bound") |> constraint_object
    @test x_z_ub.func == -100zbin + x_z
    @test x_z_ub.set == MOI.LessThan(0.)
end

function test_aggregate_variable()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    vrefs = Set([x])
    @test prep_bounds(x, model, Hull()) isa Nothing
    method = DP._Hull(Hull(1e-3), vrefs)
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing
    refcons = Vector{JuMP.AbstractConstraint}()
    DP._aggregate_variable(model, refcons, x, method)
    @test length(refcons) == 1
    @test refcons[1].func == -x + sum(method.disjunction_variables[x])
    @test refcons[1].set == MOI.EqualTo(0.)
end

function test_disaggregate_expression_var()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x])
    @test prep_bounds(x, model, Hull()) isa Nothing
    method = DP._Hull(Hull(1e-3), vrefs)
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing

    refexpr = DP.disaggregate_expression(model, x, bvrefs[z], method)
    x_z = variable_by_name(model, "x_z")
    @test refexpr == x_z
end

function test_disaggregate_expression_var_binary()
    model = GDPModel()
    @variable(model, x, Bin)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x])
    method = DP._Hull(Hull(1e-3), vrefs)
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing
    @test isnothing(variable_by_name(model, "x_z"))

    refexpr = DP.disaggregate_expression(model, x, bvrefs[z], method)
    @test refexpr == x
end

function test_disaggregate_expression_affine()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x])
    @test prep_bounds(x, model, Hull()) isa Nothing
    method = DP._Hull(Hull(1e-3), vrefs)
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing

    refexpr = DP.disaggregate_expression(model, 2x + 1, bvrefs[z], method)
    x_z = variable_by_name(model, "x_z")
    zbin = variable_by_name(model, "z")
    @test refexpr == 2x_z + 1zbin
end

function test_disaggregate_expression_affine_mip()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, y, Bin)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x, y])
    @test prep_bounds(x, model, Hull()) isa Nothing
    method = DP._Hull(Hull(1e-3), vrefs)
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing

    refexpr = DP.disaggregate_expression(model, 2x + y + 1, bvrefs[z], method)
    x_z = variable_by_name(model, "x_z")
    zbin = variable_by_name(model, "z")
    @test refexpr == 2x_z + y + 1zbin
end

function test_disaggregate_expression_quadratic()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x])
    @test prep_bounds(x, model, Hull()) isa Nothing
    method = DP._Hull(Hull(1e-3), vrefs)
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing

    refexpr = DP.disaggregate_expression(model, 2x^2 + 1, bvrefs[z], method)
    x_z = variable_by_name(model, "x_z")
    zbin = variable_by_name(model, "z")
    ϵ = method.value
    @test refexpr.head == :+
    @test 1zbin in refexpr.args
    arg2 = setdiff(refexpr.args, [1zbin])[1]
    @test arg2.head == :/
    @test 2x_z^2 in arg2.args
    @test (1-ϵ)*zbin+ϵ in arg2.args
end

function test_disaggregate_nl_expression_c()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x])
    @test prep_bounds(x, model, Hull()) isa Nothing
    method = DP._Hull(Hull(1e-3), vrefs)
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing

    refexpr = DP._disaggregate_nl_expression(model, 1, bvrefs[z], method)
    @test refexpr == 1
end

function test_disaggregate_nl_expression_var_binary()
    model = GDPModel()
    @variable(model, x, Bin)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x])
    method = DP._Hull(Hull(1e-3), vrefs)
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing

    refexpr = DP._disaggregate_nl_expression(model, x, bvrefs[z], method)
    ϵ = method.value
    @test refexpr.head == :/
    @test x in refexpr.args
    @test (1-ϵ)*bvrefs[z]+ϵ in refexpr.args
end

function test_disaggregate_nl_expression_var()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x])
    method = DP._Hull(Hull(1e-3), vrefs)
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing

    refexpr = DP._disaggregate_nl_expression(model, x, bvrefs[z], method)
    x_z = variable_by_name(model, "x_z")
    zbin = variable_by_name(model, "z")
    ϵ = method.value
    @test refexpr.head == :/
    @test x_z in refexpr.args
    @test (1-ϵ)*zbin+ϵ in refexpr.args
end

function test_disaggregate_nl_expression_aff()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x])
    method = DP._Hull(Hull(1e-3), vrefs)
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing

    refexpr = DP._disaggregate_nl_expression(model, 2x + 1, bvrefs[z], method)
    x_z = variable_by_name(model, "x_z")
    zbin = variable_by_name(model, "z")
    ϵ = method.value
    @test refexpr.head == :+
    @test 1 in refexpr.args
    arg2 = setdiff(refexpr.args, [1])[1]
    @test arg2.head == :/
    @test 2x_z in arg2.args
    @test (1-ϵ)*zbin+ϵ in arg2.args
end

function test_disaggregate_nl_expression_aff_mip()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, y, Bin)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x,y])
    method = DP._Hull(Hull(1e-3), vrefs)
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing

    refexpr = DP._disaggregate_nl_expression(model, 2x + y + 1, bvrefs[z], method)
    flatten!(refexpr)
    x_z = variable_by_name(model, "x_z")
    zbin = variable_by_name(model, "z")
    ϵ = method.value
    @test refexpr.head == :+
    @test 1 in refexpr.args
    args2 = setdiff(refexpr.args, [1])
    for arg in args2
        @test arg.head == :/
        @test 2x_z in arg.args || 1y in arg.args
        @test (1-ϵ)*zbin+ϵ in arg.args
    end
end

function test_disaggregate_nl_expression_quad()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x])
    method = DP._Hull(Hull(1e-3), vrefs)
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing

    refexpr = DP._disaggregate_nl_expression(model, 2x^2 + 1, bvrefs[z], method)
    x_z = variable_by_name(model, "x_z")
    zbin = variable_by_name(model, "z")
    ϵ = method.value
    @test refexpr.head == :+
    @test 1 in refexpr.args
    arg2 = setdiff(refexpr.args, [1])[1]
    @test arg2.head == :/
    @test 2x_z^2 in arg2.args
    @test ((1-ϵ)*zbin+ϵ)^2 in arg2.args
end

function test_disaggregate_nl_expession()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    bvrefs = DP._indicator_to_binary(model)

    vrefs = Set([x])
    method = DP._Hull(Hull(1e-3), vrefs)
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, vrefs, method) isa Nothing

    refexpr = DP._disaggregate_nl_expression(model, 2x^3 + 1, bvrefs[z], method)
    x_z = variable_by_name(model, "x_z")
    zbin = variable_by_name(model, "z")
    ϵ = method.value
    @test refexpr.head == :+
    @test 1 in refexpr.args
    arg2 = setdiff(refexpr.args, [1zbin])[1]
    @test arg2.head == :*
    @test 2 in arg2.args
    arg3 = setdiff(arg2.args, [2])[1]
    @test arg3.head == :^
    @test arg3.args[2] == 3
    @test arg3.args[1].head == :/
    @test x_z in arg3.args[1].args
    @test (1-ϵ)*zbin+ϵ in arg3.args[1].args
end
#less than, greater than, equalto
function test_scalar_var_hull_1sided(moiset)
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, x in moiset(5), Disjunct(z))
    zbin = variable_by_name(model, "z")
    @test prep_bounds(x, model, Hull()) isa Nothing
    method = DP._Hull(Hull(1e-3), Set([x]))
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test ref[1].func == x_z - 5*zbin
    @test ref[1].set isa moiset
    @test DP._set_value(ref[1].set) == 0
end
#less than, greater than, equalto
function test_scalar_affine_hull_1sided(moiset)
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, 1x in moiset(5), Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(1e-3), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test ref[1].func == x_z - 5*zbin
    @test ref[1].set isa moiset
    @test DP._set_value(ref[1].set) == 0
end
#nonpositives, nonnegatives, zeros
function test_vector_var_hull_1sided(moiset)
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, [x; x] in moiset(2), Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(1e-3), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test ref[1].func == [x_z; x_z]
    @test ref[1].set == moiset(2)
end
#nonpositives, nonnegatives, zeros
function test_vector_affine_hull_1sided(moiset)
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, [x - 5; x - 5] in moiset(2), Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(1e-3), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test ref[1].func == [x_z - 5*zbin; x_z - 5*zbin]
    @test ref[1].set == moiset(2)
end
#less than, greater than, equalto
function test_scalar_quadratic_hull_1sided(moiset)
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, x^2 in moiset(5), Disjunct(z))
    zbin = variable_by_name(model, "z")
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    A = (x_z^2 / ((1 - ϵ) * zbin + ϵ)) - (5 * zbin)
    B = (zero(AffExpr) + (x_z^2 / ((1 - ϵ) * zbin + ϵ))) - (5 * zbin)
    @test isequal_canonical(ref[1].func, A) || isequal_canonical(ref[1].func, B)
    return
end
#nonpositives, nonnegatives, zeros
function test_vector_quadratic_hull_1sided(moiset)
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, [x^2 - 5; x^2 - 5] in moiset(2), Disjunct(z))
    zbin = variable_by_name(model, "z")
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test length(ref[1].func) == 2
    for i in 1:2
        @test ref[1].func[i].head == :+
        @test -5zbin in ref[1].func[i].args
        arg2 = setdiff(ref[1].func[i].args, [-5zbin])[1]
        @test arg2.head == :/
        @test x_z^2 in arg2.args
        @test (1-ϵ)*zbin+ϵ in arg2.args
    end
    @test ref[1].set == moiset(2)
end
#less than, greater than, equalto
function test_scalar_nonlinear_hull_1sided_error()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, log(x) <= 10, Disjunct(z))
    zbin = variable_by_name(model, "z")
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    @test_throws ErrorException reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
end
function test_scalar_nonlinear_hull_1sided(moiset)
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, x^3 in moiset(5), Disjunct(z))
    zbin = variable_by_name(model, "z")
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test ref[1].func.head == :-
    @test 5zbin in ref[1].func.args
    arg2 = setdiff(ref[1].func.args, [5zbin])[1]
    @test 0*zbin in arg2.args
    arg3 = setdiff(arg2.args, [0*zbin])[1]
    @test arg3.head == :*
    @test (1-ϵ)*zbin+ϵ in arg3.args
    arg4 = setdiff(arg3.args, [(1-ϵ)*zbin+ϵ])[1]
    @test arg4.head == :^
    @test arg4.args[2] == 3
    @test arg4.args[1].head == :/
    @test x_z in arg4.args[1].args
    @test (1-ϵ)*zbin+ϵ in arg4.args[1].args
    @test ref[1].set isa moiset
    @test DP._set_value(ref[1].set) == 0
end
#nonpositives, nonnegatives, zeros
function test_vector_nonlinear_hull_1sided_error()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, [log(x),log(x)] <= [10,10], Disjunct(z))
    zbin = variable_by_name(model, "z")
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    @test_throws ErrorException reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
end
function test_vector_nonlinear_hull_1sided(moiset)
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, [x^3 - 5; x^3 - 5] in moiset(2), Disjunct(z))
    zbin = variable_by_name(model, "z")
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test length(ref[1].func) == 2
    for i in 1:2
        @test ref[1].func[i].head == :-
        @test -5*ϵ*(1-zbin) in ref[1].func[i].args
        arg2 = setdiff(ref[1].func[i].args, [-5*ϵ*(1-zbin)])[1]
        @test arg2.head == :*
        @test (1-ϵ)*zbin+ϵ in arg2.args
        arg3 = setdiff(arg2.args, [(1-ϵ)*zbin+ϵ])[1]
        @test arg3.head == :-
        @test 5 in arg3.args
        arg4 = setdiff(arg3.args, [5])[1]
        @test arg4.head == :^
        @test arg4.args[2] == 3
        @test arg4.args[1].head == :/
        @test x_z in arg4.args[1].args
        @test (1-ϵ)*zbin+ϵ in arg4.args[1].args
    end
    @test ref[1].set == moiset(2)
end
#interval
function test_scalar_var_hull_2sided()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, x in MOI.Interval(5,5), Disjunct(z))
    zbin = variable_by_name(model, "z")
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 2
    sets = (MOI.GreaterThan, MOI.LessThan)
    for i in 1:2
        @test ref[i].func == x_z - 5*zbin
        @test ref[i].set isa sets[i]
        @test DP._set_value(ref[1].set) == 0
    end
end
function test_scalar_affine_hull_2sided()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, 5 <= x <= 5, Disjunct(z))
    zbin = variable_by_name(model, "z")
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 2
    sets = (MOI.GreaterThan, MOI.LessThan)
    for i in 1:2
        @test ref[i].func == x_z - 5*zbin
        @test ref[i].set isa sets[i]
        @test DP._set_value(ref[1].set) == 0
    end
end
function test_scalar_quadratic_hull_2sided()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, 5 <= x^2 <= 5, Disjunct(z))
    zbin = variable_by_name(model, "z")
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 2
    sets = (MOI.GreaterThan, MOI.LessThan)
    A = (x_z^2 / ((1 - ϵ) * zbin + ϵ)) - (5 * zbin)
    B = (zero(AffExpr) + (x_z^2 / ((1 - ϵ) * zbin + ϵ))) - (5 * zbin)
    for (r, S) in zip(ref, sets)
        @test isequal_canonical(r.func, A) || isequal_canonical(r.func, B)
        @test r.set isa S
        @test DP._set_value(r.set) == 0
    end
    return
end
function test_scalar_nonlinear_hull_2sided_error()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, 0 <= log(x) <= 10, Disjunct(z))
    zbin = variable_by_name(model, "z")
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    @test_throws ErrorException reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
end
function test_scalar_nonlinear_hull_2sided()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, 5 <= x^3 <= 5, Disjunct(z))
    zbin = variable_by_name(model, "z")
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    @test prep_bounds(x, model, Hull()) isa Nothing
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 2
    sets = (MOI.GreaterThan, MOI.LessThan)
    for i in 1:2
        @test ref[i].func.head == :-
        @test 5zbin in ref[i].func.args
        arg2 = setdiff(ref[i].func.args, [5zbin])[1]
        @test 0*zbin in arg2.args
        arg3 = setdiff(arg2.args, [0*zbin])[1]
        @test arg3.head == :*
        @test (1-ϵ)*zbin+ϵ in arg3.args
        arg4 = setdiff(arg3.args, [(1-ϵ)*zbin+ϵ])[1]
        @test arg4.head == :^
        @test arg4.args[2] == 3
        @test arg4.args[1].head == :/
        @test x_z in arg4.args[1].args
        @test (1-ϵ)*zbin+ϵ in arg4.args[1].args
        @test ref[i].set isa sets[i]
        @test DP._set_value(ref[i].set) == 0
    end
end

function test_exactly1_error()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, z[1:2], Logical)
    @constraint(model, 1 <= x <= 5, Disjunct(z[1]))
    @constraint(model, 3 <= x <= 5, Disjunct(z[2]))
    disjunction(model, z, exactly1 = false)
    @test requires_exactly1(Hull())
    @test_throws ErrorException reformulate_model(model, Hull())
end

function test_extension_hull()
    # test error for hull
    @test_throws ErrorException requires_disaggregation(BadVarRef())

    # prepare extension model
    model = GDPModel{MyModel, MyVarRef, MyConRef}()
    @variable(model, -100 <= x <= 100)
    @variable(model, y[1:2], Logical(MyVar))
    @variable(model, z[1:2], Logical(MyVar))
    @constraint(model, x <= 5, Disjunct(y[1]))
    @constraint(model, x >= 5, Disjunct(y[2]))
    @disjunction(model, inner, y, Disjunct(z[1]))
    @constraint(model, x <= 10, Disjunct(z[1]))
    @constraint(model, x >= 10, Disjunct(z[2]))
    @disjunction(model, outer, z)

    # test reformulation
    @test reformulate_model(model, Hull()) isa Nothing
    refcons = constraint_object.(DP._reformulation_constraints(model))
    @test length(refcons) == 16
    @test length(DP._reformulation_variables(model)) == 4
    # TODO add more tests
end

function test_vector_soc_hull()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, 10 <= t <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, [t - 5, x - 5] in SecondOrderCone(), Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(1e-3), Set([x, t]))
    prep_bounds([x, t], model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x, t]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    t_z = variable_by_name(model, "t_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test ref[1].func == [t_z - 5*zbin, x_z - 5*zbin]
    @test ref[1].set == MOI.SecondOrderCone(2)
end

function test_vector_rsoc_hull()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, 10 <= t <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, [0.5, t - 2, x - 3] in RotatedSecondOrderCone(), Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(1e-3), Set([x, t]))
    prep_bounds([x, t], model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x, t]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    t_z = variable_by_name(model, "t_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test ref[1].func == [0.5*zbin, t_z - 2*zbin, x_z - 3*zbin]
    @test ref[1].set == MOI.RotatedSecondOrderCone(3)
end

function test_vector_exp_hull()
    model = GDPModel()
    @variable(model, 10 <= x <= 100)
    @variable(model, 10 <= t <= 100)
    @variable(model, 10 <= w <= 100)
    @variable(model, z, Logical)
    @constraint(model, con, [x - 1, t - 1, w - 1] in MOI.ExponentialCone(), Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(1e-3), Set([x, t, w]))
    prep_bounds([x, t, w], model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x, t, w]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    t_z = variable_by_name(model, "t_z")
    w_z = variable_by_name(model, "w_z")
    ref = reformulate_disjunct_constraint(model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test ref[1].func == [x_z - zbin, t_z - zbin, w_z - zbin]
    @test ref[1].set == MOI.ExponentialCone()
end

function test_hull_quadratic_option_error()
    @test_throws ErrorException Hull(quadratic = :bad_option)
    @test Hull().quadratic == :epsilon
    @test Hull(1e-3, quadratic = :exact).quadratic == :exact
end
#less than, greater than, equalto with GEHR forced
function test_scalar_gehr_hull_1sided(moiset)
    model = GDPModel()
    @variable(model, -2 <= x <= 3)
    @variable(model, z, Logical)
    @constraint(model, con, x^2 + 3x in moiset(5), Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(quadratic = :gehr), Set([x]))
    prep_bounds(x, model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    gehr = x_z^2 + 3*x_z*zbin - 5*zbin^2
    if moiset == MOI.GreaterThan # flipped to h(x) ≤ 0
        @test isequal_canonical(ref[1].func, -gehr)
        @test ref[1].set == MOI.LessThan(0.0)
    else
        @test isequal_canonical(ref[1].func, gehr)
        expected = moiset == MOI.EqualTo ? MOI.EqualTo(0.0) :
            MOI.LessThan(0.0)
        @test ref[1].set == expected
    end
end
#convex quadratic routed to CEHR under :exact
function test_scalar_cehr_hull()
    model = GDPModel()
    @variable(model, -2 <= x <= 3)
    @variable(model, z, Logical)
    @constraint(model, con, x^2 + 3x <= 5, Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(quadratic = :exact), Set([x]))
    prep_bounds(x, model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, method)
    @test length(ref) == 2
    t = variable_by_name(model, "t_cehr_z")
    @test lower_bound(t) == 0
    @test isequal_canonical(ref[1].func, x_z^2 - t*zbin)
    @test ref[1].set == MOI.LessThan(0.0)
    @test isequal_canonical(ref[2].func, t + 3*x_z - 5*zbin)
    @test ref[2].set == MOI.LessThan(0.0)
end
#concave greater-than flips to a convex constraint and routes to CEHR
function test_scalar_cehr_hull_concave_greater()
    model = GDPModel()
    @variable(model, -2 <= x <= 3)
    @variable(model, z, Logical)
    @constraint(model, con, -x^2 + 3x >= 1, Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(quadratic = :exact), Set([x]))
    prep_bounds(x, model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, method)
    @test length(ref) == 2
    t = variable_by_name(model, "t_cehr_z")
    @test isequal_canonical(ref[1].func, x_z^2 - t*zbin)
    @test isequal_canonical(ref[2].func, t - 3*x_z + 1*zbin)
end
#cehr_conic writes the cone out as an explicit rotated SOC
function test_scalar_cehr_conic_hull()
    model = GDPModel()
    @variable(model, -2 <= x <= 3)
    @variable(model, z, Logical)
    @constraint(model, con, x^2 + 3x <= 5, Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(quadratic = :cehr_conic), Set([x]))
    prep_bounds(x, model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, method)
    @test length(ref) == 2
    t = variable_by_name(model, "t_cehr_z")
    @test lower_bound(t) == 0
    @test ref[1].set == MOI.RotatedSecondOrderCone(3)
    @test isequal_canonical(ref[1].func[1], 0.5 * t)
    @test isequal_canonical(ref[1].func[2], 1.0 * zbin)
    # eigenvector sign is implementation-defined
    @test abs(coefficient(ref[1].func[3], x_z)) ≈ 1.0
    @test isequal_canonical(ref[2].func, t + 3*x_z - 5*zbin)
    @test ref[2].set == MOI.LessThan(0.0)
end
#singular Q drops its zero eigenvalue rows from the cone
function test_scalar_cehr_conic_rank_deficient()
    model = GDPModel()
    @variable(model, -2 <= x <= 3)
    @variable(model, -2 <= w <= 3)
    @variable(model, z, Logical)
    @constraint(model, con, (x + w)^2 <= 4, Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(quadratic = :cehr_conic), Set([x, w]))
    prep_bounds([x, w], model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x, w]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    w_z = variable_by_name(model, "w_z")
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, method)
    @test ref[1].set == MOI.RotatedSecondOrderCone(3) # rank 1, not 2
    row = ref[1].func[3]
    s = sign(coefficient(row, x_z))
    @test coefficient(row, x_z) ≈ s * 1.0
    @test coefficient(row, w_z) ≈ s * 1.0
end
#cehr_conic rejects nonconvex and equality constraints like cehr
function test_scalar_cehr_conic_errors()
    model = GDPModel()
    @variable(model, -2 <= x <= 3)
    @variable(model, -2 <= w <= 3)
    @variable(model, z, Logical)
    @constraint(model, con, x*w <= 5, Disjunct(z))
    @constraint(model, con_eq, x^2 == 4, Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(quadratic = :cehr_conic), Set([x, w]))
    prep_bounds([x, w], model, Hull())
    DP._disaggregate_variables(model, z, Set([x, w]), method)
    @test_throws ErrorException reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, method)
    @test_throws ErrorException reformulate_disjunct_constraint(
        model, constraint_object(con_eq), zbin, method)
end
#all quadratic terms are pure on normal models, rest keeps the affine
function test_split_quad_terms()
    model = GDPModel()
    @variable(model, x)
    @variable(model, w)
    quad = @expression(model, x^2 + 2*x*w + 3*x + 2)
    quad_part, affine_part = DP._split_quad_terms(quad)
    @test isequal_canonical(quad_part, @expression(model, x^2 + 2*x*w))
    @test isempty(affine_part.terms)
    @test isequal_canonical(affine_part.aff, @expression(model, 3*x + 2))
end
#nonconvex quadratic routed to GEHR under :exact, error under :cehr
function test_scalar_exact_hull_nonconvex()
    model = GDPModel()
    @variable(model, -2 <= x <= 3)
    @variable(model, -2 <= w <= 3)
    @variable(model, z, Logical)
    @constraint(model, con, x*w <= 5, Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(quadratic = :exact), Set([x, w]))
    prep_bounds([x, w], model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x, w]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    w_z = variable_by_name(model, "w_z")
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test isequal_canonical(ref[1].func, x_z*w_z - 5*zbin^2)
    @test ref[1].set == MOI.LessThan(0.0)
    forced = DP._Hull(Hull(quadratic = :cehr), Set([x, w]))
    forced.disjunct_variables = method.disjunct_variables
    @test_throws ErrorException reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, forced)
end
#quadratic equality reformulated by GEHR, error under :cehr
function test_scalar_exact_hull_equality()
    model = GDPModel()
    @variable(model, -2 <= x <= 3)
    @variable(model, z, Logical)
    @constraint(model, con, x^2 == 5, Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(quadratic = :exact), Set([x]))
    prep_bounds(x, model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, method)
    @test length(ref) == 1
    @test isequal_canonical(ref[1].func, x_z^2 - 5*zbin^2)
    @test ref[1].set == MOI.EqualTo(0.0)
    forced = DP._Hull(Hull(quadratic = :cehr), Set([x]))
    forced.disjunct_variables = method.disjunct_variables
    @test_throws ErrorException reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, forced)
end
#interval: CEHR on the upper side, GEHR on the (nonconvex) lower side
function test_scalar_exact_hull_2sided()
    model = GDPModel()
    @variable(model, -2 <= x <= 3)
    @variable(model, z, Logical)
    @constraint(model, con, 2 <= x^2 <= 5, Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(quadratic = :exact), Set([x]))
    prep_bounds(x, model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, method)
    @test length(ref) == 3
    t = variable_by_name(model, "t_cehr_z")
    @test isequal_canonical(ref[1].func, x_z^2 - t*zbin)
    @test ref[1].set == MOI.LessThan(0.0)
    @test isequal_canonical(ref[2].func, t - 5*zbin)
    @test ref[2].set == MOI.LessThan(0.0)
    @test isequal_canonical(ref[3].func, -x_z^2 + 2*zbin^2)
    @test ref[3].set == MOI.LessThan(0.0)
end
#nonpositives, nonnegatives, zeros with exact reformulations
function test_vector_exact_hull_1sided(moiset)
    model = GDPModel()
    @variable(model, -2 <= x <= 3)
    @variable(model, z, Logical)
    @constraint(model, con, [x^2 - 5; x^2 - 5] in moiset(2), Disjunct(z))
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(quadratic = :exact), Set([x]))
    prep_bounds(x, model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), zbin, method)
    if moiset == MOI.Nonpositives # convex entries: CEHR per entry
        @test length(ref) == 4
        @test all(r.set == MOI.LessThan(0.0) for r in ref)
        tvars = filter(v -> startswith(name(v), "t_cehr"), all_variables(model))
        @test length(tvars) == 2
        @test all(lower_bound(t) == 0 for t in tvars)
    elseif moiset == MOI.Nonnegatives # flipped: nonconvex, GEHR
        @test length(ref) == 2
        for i in 1:2
            @test isequal_canonical(ref[i].func, -x_z^2 + 5*zbin^2)
            @test ref[i].set == MOI.LessThan(0.0)
        end
    else # Zeros: equalities, GEHR
        @test length(ref) == 2
        for i in 1:2
            @test isequal_canonical(ref[i].func, x_z^2 - 5*zbin^2)
            @test ref[i].set == MOI.EqualTo(0.0)
        end
    end
end
#quadratic expression without quadratic terms falls back to affine hull
function test_exact_hull_affine_fallback()
    model = GDPModel()
    @variable(model, -2 <= x <= 3)
    @variable(model, z, Logical)
    zbin = variable_by_name(model, "z")
    method = DP._Hull(Hull(quadratic = :exact), Set([x]))
    prep_bounds(x, model, Hull())
    @test DP._disaggregate_variables(model, z, Set([x]), method) isa Nothing
    x_z = variable_by_name(model, "x_z")
    con = JuMP.build_constraint(
        error, convert(QuadExpr, 2.0x + 1.0), MOI.LessThan(5.0))
    ref = reformulate_disjunct_constraint(model, con, zbin, method)
    @test length(ref) == 1
    @test isequal_canonical(ref[1].func, 2*x_z + 1*zbin - 5*zbin)
    @test ref[1].set == MOI.LessThan(0.0)
    con = JuMP.build_constraint(
        error, convert(QuadExpr, 2.0x + 1.0), MOI.EqualTo(5.0))
    ref = reformulate_disjunct_constraint(model, con, zbin, method)
    @test length(ref) == 1
    @test isequal_canonical(ref[1].func, 2*x_z + 1*zbin - 5*zbin)
    @test ref[1].set == MOI.EqualTo(0.0)
end

@testset "Hull Reformulation" begin
    test_default_hull()
    test_set_hull()
    test_query_variable_bounds()
    test_query_variable_bounds_error1()
    test_query_variable_bounds_error2()
    test_disaggregate_variables()
    test_aggregate_variable()
    test_disaggregate_expression_var()
    test_disaggregate_expression_var_binary()
    test_disaggregate_expression_affine()
    test_disaggregate_expression_affine_mip()
    test_disaggregate_expression_quadratic()
    test_disaggregate_nl_expression_c()
    test_disaggregate_nl_expression_var()
    test_disaggregate_nl_expression_var_binary()
    test_disaggregate_nl_expression_aff()
    test_disaggregate_nl_expression_aff_mip()
    test_disaggregate_nl_expression_quad()
    test_disaggregate_nl_expession()
    for s in (MOI.LessThan, MOI.GreaterThan, MOI.EqualTo)
        test_scalar_var_hull_1sided(s)
        test_scalar_affine_hull_1sided(s)
        test_scalar_quadratic_hull_1sided(s)
        test_scalar_gehr_hull_1sided(s)
        test_scalar_nonlinear_hull_1sided(s)
    end
    test_scalar_nonlinear_hull_1sided_error()
    for s in (MOI.Nonpositives, MOI.Nonnegatives, MOI.Zeros)
        test_vector_var_hull_1sided(s)
        test_vector_affine_hull_1sided(s)
        test_vector_quadratic_hull_1sided(s)
        test_vector_exact_hull_1sided(s)
        test_vector_nonlinear_hull_1sided(s)
    end
    test_vector_nonlinear_hull_1sided_error()
    test_scalar_var_hull_2sided()
    test_scalar_affine_hull_2sided()
    test_scalar_quadratic_hull_2sided()
    test_scalar_nonlinear_hull_2sided()
    test_scalar_nonlinear_hull_2sided_error()
    test_hull_quadratic_option_error()
    test_split_quad_terms()
    test_scalar_cehr_hull()
    test_scalar_cehr_hull_concave_greater()
    test_scalar_cehr_conic_hull()
    test_scalar_cehr_conic_rank_deficient()
    test_scalar_cehr_conic_errors()
    test_scalar_exact_hull_nonconvex()
    test_scalar_exact_hull_equality()
    test_scalar_exact_hull_2sided()
    test_exact_hull_affine_fallback()
    test_exactly1_error()
    test_extension_hull()
    test_vector_soc_hull()
    test_vector_rsoc_hull()
    test_vector_exp_hull()
end
