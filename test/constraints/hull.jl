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
    @test ref[1].func.head == :-
    @test 5zbin in ref[1].func.args
    arg2 = setdiff(ref[1].func.args, [5zbin])[1]
    @test 0*zbin in arg2.args
    arg3 = setdiff(arg2.args, [0*zbin])[1]
    @test arg3.head == :/
    @test x_z^2 in arg3.args
    @test (1-ϵ)*zbin+ϵ in arg3.args
    @test ref[1].set isa moiset
    @test DP._set_value(ref[1].set) == 0
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
    for i in 1:2
        @test ref[i].func.head == :-
        @test 5zbin in ref[i].func.args
        arg2 = setdiff(ref[i].func.args, [5zbin])[1]
        @test 0*zbin in arg2.args
        arg3 = setdiff(arg2.args, [0*zbin])[1]
        @test arg3.head == :/
        @test x_z^2 in arg3.args
        @test (1-ϵ)*zbin+ϵ in arg3.args
        @test ref[i].set isa sets[i]
        @test DP._set_value(ref[i].set) == 0
    end
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
        test_scalar_nonlinear_hull_1sided(s)
    end
    test_scalar_nonlinear_hull_1sided_error()
    for s in (MOI.Nonpositives, MOI.Nonnegatives, MOI.Zeros)
        test_vector_var_hull_1sided(s)
        test_vector_affine_hull_1sided(s)
        test_vector_quadratic_hull_1sided(s)        
        test_vector_nonlinear_hull_1sided(s)
    end
    test_vector_nonlinear_hull_1sided_error()
    test_scalar_var_hull_2sided()
    test_scalar_affine_hull_2sided()
    test_scalar_quadratic_hull_2sided()
    test_scalar_nonlinear_hull_2sided()
    test_scalar_nonlinear_hull_2sided_error()
    test_exactly1_error()
    test_extension_hull()
end