using InfiniteOpt, HiGHS, Ipopt, Juniper, Interpolations
import DisjunctiveProgramming as DP

# Helper to access internal function
const IDP = Base.get_extension(DP, :InfiniteDisjunctiveProgramming)

function test_infiniteopt_extension()
    # Initialize the model
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_attribute(model, MOI.Silent(), true)

    # Create the infinite variables
    I = 1:4
    @infinite_parameter(model, t ∈ [0, 1], num_supports = 100)
    @variable(model, 0 <= g[I] <= 10, Infinite(t))

    # Add the disjunctions and their indicator variables
    @variable(model, G[I, 1:2], InfiniteLogical(t))
    @test all(isa.(@constraint(model, [i ∈ I, j ∈ 1:2], 0 <= g[i], 
        Disjunct(G[i, 1])), DisjunctConstraintRef{InfiniteModel})
        )
    @test all(isa.(@constraint(model, [i ∈ I, j ∈ 1:2], g[i] <= 0, 
        Disjunct(G[i, 2])), DisjunctConstraintRef{InfiniteModel})
        )
    @test all(isa.(@disjunction(model, [i ∈ I], G[i, :]), 
        DisjunctionRef{InfiniteModel})
        )

    # Add the logical propositions
    @variable(model, W, InfiniteLogical(t))
    @test @constraint(model, G[1, 1] ∨ G[2, 1] ∧ G[3, 1] == W := true) isa 
        LogicalConstraintRef{InfiniteModel}
    @constraint(model, 𝔼(binary_variable(W), t) >= 0.95)

    # Reformulate and solve 
    @test optimize!(model, gdp_method = Hull()) isa Nothing

    # check the results
    @test all(value(W))
end

function test_infinite_gdp_model_creation()
    model = InfiniteGDPModel()
    @test model isa InfiniteModel
    @test is_gdp_model(model)
    
end

function test_infinite_logical()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    
    @variable(model, y, InfiniteLogical(t))
    @test y isa DP.LogicalVariableRef{InfiniteModel}
    @test binary_variable(y) isa InfiniteOpt.GeneralVariableRef
end

function test__is_parameter()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @infinite_parameter(model, s[1:2] ∈ [0, 1], independent = true)
    @finite_parameter(model, p == 1.0)
    @variable(model, x, Infinite(t))
    @variable(model, y)
    
    # Test DependentParameterRef
    @test IDP._is_parameter(t) == true
    
    # Test IndependentParameterRef
    @test IDP._is_parameter(s[1]) == true
    
    # Test FiniteParameterRef
    @test IDP._is_parameter(p) == true
    
    # Test non-parameter variables (else branch)
    @test IDP._is_parameter(x) == false
    @test IDP._is_parameter(y) == false
end

# _is_parameter on unwrapped concrete dispatch types. Covers
# ext lines 28-32 (DependentParameterRef, IndependentParameterRef,
# FiniteParameterRef, ParameterFunctionRef, Any fallback).
function test__is_parameter_concrete_dispatches()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @infinite_parameter(model, s[1:2] ∈ [0, 1], independent = true)
    @finite_parameter(model, p == 1.0)
    @variable(model, x, Infinite(t))
    @parameter_function(model, pf == t -> 2*t)
    dvr = InfiniteOpt.dispatch_variable_ref
    @test IDP._is_parameter(dvr(t)) == true      # Dependent
    @test IDP._is_parameter(dvr(s[1])) == true    # Independent
    @test IDP._is_parameter(dvr(p)) == true       # Finite
    @test IDP._is_parameter(dvr(pf)) == true      # ParamFunc
    @test IDP._is_parameter(dvr(x)) == false      # Any
end

function test_requires_disaggregation()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @finite_parameter(model, p == 1.0)
    @variable(model, x, Infinite(t))
    @variable(model, y)
    
    # Parameters should NOT require disaggregation
    @test DP.requires_disaggregation(t) == false
    @test DP.requires_disaggregation(p) == false
    
    # Variables SHOULD require disaggregation
    @test DP.requires_disaggregation(x) == true
    @test DP.requires_disaggregation(y) == true
end

function test_all_variables_infiniteopt()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @variable(model, x, Infinite(t))
    @variable(model, y)
    @variable(model, dx, Infinite(t))
    @deriv(dx, t)
    
    all_vars = DP.collect_all_vars(model)
    @test x in all_vars
    @test y in all_vars
    @test dx in all_vars
    
    # Verify derivatives are included
    derivs = collect(InfiniteOpt.all_derivatives(model))
    for d in derivs
        @test d in all_vars
    end
end

function test_get_constant()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @finite_parameter(model, p == 2.0)
    @variable(model, x, Infinite(t))
    
    # Test expression with parameter terms (_is_parameter branch)
    expr2 = @expression(model, 3.0 + 2*t + x)
    constant2 = DP.get_constant(expr2)
    @test JuMP.constant(constant2) == 3.0
    @test haskey(constant2.terms, t)
    @test constant2.terms[t] == 2.0
    @test !haskey(constant2.terms, x)
    
    # Test expression with finite parameter
    expr3 = @expression(model, 1.0 + 3*p)
    constant3 = DP.get_constant(expr3)
    @test JuMP.constant(constant3) == 1.0
    @test haskey(constant3.terms, p)
    @test constant3.terms[p] == 3.0
end

function test_disaggregate_expression_infiniteopt()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, z, InfiniteLogical(t))
    @variable(model, w, Bin)
    
    bvrefs = DP._indicator_to_binary(model)
    bvref = bvrefs[z]
    
    vrefs = Set([x, w])
    DP._variable_bounds(model)[x] = DP.set_variable_bound_info(x, Hull())
    method = DP._Hull(Hull(1e-3), vrefs)
    DP._disaggregate_variables(model, z, vrefs, method)
    
    aff_bin = @expression(model, 2*w + 1)
    result_bin = DP.disaggregate_expression(model, aff_bin, bvref, method)
    @test haskey(result_bin.terms, w)
    
    aff_param = @expression(model, 3*t + 1)
    result_param = DP.disaggregate_expression(model, aff_param, bvref, method)
    @test result_param isa JuMP.GenericQuadExpr
    
    aff_expr = @expression(model, 2*x + 1)
    result_expr = DP.disaggregate_expression(model, aff_expr, bvref, method)
    dvref = method.disjunct_variables[x, bvref]
    @test result_expr == bvref + 2*dvref
    
    @variable(model, 0 <= y <= 5, Infinite(t))
    aff_not_disagg = @expression(model, 3*y + 1)
    result_not_disagg = DP.disaggregate_expression(model, aff_not_disagg, bvref, method)
    @test haskey(result_not_disagg.terms, y)
end

function test_disaggregate_quad_expression_infiniteopt()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, 0 <= y <= 5, Infinite(t))
    @variable(model, z, InfiniteLogical(t))

    bvrefs = DP._indicator_to_binary(model)
    bvref = bvrefs[z]

    vrefs = Set([x, y])
    DP._variable_bounds(model)[x] = DP.set_variable_bound_info(x, Hull())
    DP._variable_bounds(model)[y] = DP.set_variable_bound_info(y, Hull())
    method = DP._Hull(Hull(1e-3), vrefs)
    DP._disaggregate_variables(model, z, vrefs, method)

    # var × var → nonlinear (perspective divides by y)
    quad_vv = @expression(model, x * y)
    result_vv = DP.disaggregate_expression(model, quad_vv, bvref, method)
    @test result_vv isa JuMP.GenericNonlinearExpr

    # param × var → quadratic (param * disaggregated)
    quad_pv = @expression(model, t * x)
    result_pv = DP.disaggregate_expression(model, quad_pv, bvref, method)
    @test result_pv isa JuMP.GenericQuadExpr

    # var × param → quadratic (disaggregated * param)
    quad_vp = @expression(model, x * t)
    result_vp = DP.disaggregate_expression(model, quad_vp, bvref, method)
    @test result_vp isa JuMP.GenericQuadExpr

    # param × param → cubic (t * t * bvref)
    quad_pp = @expression(model, t * t)
    result_pp = DP.disaggregate_expression(model, quad_pp, bvref, method)
    @test result_pp isa JuMP.GenericNonlinearExpr
end

function test_variable_properties_infiniteopt()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @variable(model, 1 <= x <= 10, Infinite(t), start = 5.0)
    @variable(model, y)
    
    props_x = DP.VariableProperties(x)
    @test props_x.info.has_lb == true
    @test props_x.info.lower_bound == 1.0
    @test props_x.info.has_ub == true
    @test props_x.info.upper_bound == 10.0
    @test props_x.name == "x"
    @test props_x.set === nothing
    @test t in InfiniteOpt.parameter_refs(x)
    
    props_y = DP.VariableProperties(y)
    @test props_y.name == "y"
    @test props_y.variable_type === nothing
end

function test_variable_properties_from_expr()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @infinite_parameter(model, s ∈ [0, 2])
    @variable(model, x, Infinite(t))
    @variable(model, y, Infinite(s))
    
    expr = @expression(model, 2*x + y)
    props = DP.VariableProperties(expr)
    @test props.name == ""
    @test props.variable_type isa InfiniteOpt.Infinite
    @test Set(props.variable_type.parameter_refs) == Set((t, s))
    var1 = DP.create_variable(model, props)
    JuMP.set_name(var1, "inferred_var")
    @test JuMP.name(var1) == "inferred_var"
    @test InfiniteOpt.parameter_refs(var1) == (t, s)
end

function test_variable_properties_from_quad_expr()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @infinite_parameter(model, s ∈ [0, 2])
    @variable(model, x, Infinite(t))
    @variable(model, y, Infinite(s))
    
    expr = @expression(model, x^2 + x*y)
    props = DP.VariableProperties(expr)
    @test props.name == ""
    @test props.variable_type isa InfiniteOpt.Infinite
    @test Set(props.variable_type.parameter_refs) == Set((t, s))
    var1 = DP.create_variable(model, props)
    JuMP.set_name(var1, "quad_inferred_var")
    @test JuMP.name(var1) == "quad_inferred_var"
    @test Set(InfiniteOpt.parameter_refs(var1)) == Set((t, s))
end

function test_variable_properties_from_nonlinear_expr()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @infinite_parameter(model, s ∈ [0, 2])
    @variable(model, x, Infinite(t))
    @variable(model, y, Infinite(s))

    expr = @expression(model, exp(x) + sin(y))
    props = DP.VariableProperties(expr)
    @test props.name == ""
    @test props.variable_type isa InfiniteOpt.Infinite
    @test Set(props.variable_type.parameter_refs) == Set((t, s))
    var1 = DP.create_variable(model, props)
    JuMP.set_name(var1, "nl_inferred_var")
    @test JuMP.name(var1) == "nl_inferred_var"
    @test Set(InfiniteOpt.parameter_refs(var1)) == Set((t, s))
end

function test_variable_properties_from_vector()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @infinite_parameter(model, s ∈ [0, 2])
    @infinite_parameter(model, r ∈ [0, 3])
    @variable(model, x, Infinite(t))
    @variable(model, y, Infinite(s))
    @variable(model, z, Infinite(r))

    exprs = [
        @expression(model, x + 1),
        @expression(model, y + 2),
        @expression(model, exp(z))
    ]
    props = DP.VariableProperties(exprs)
    var1 = DP.create_variable(model, props)
    JuMP.set_name(var1, "vector_var")
    @test JuMP.name(var1) == "vector_var"
    prefs = InfiniteOpt.parameter_refs(var1)
    @test length(prefs) == 3
    @test Set(prefs) == Set((t, s, r))
end

function test_add_cardinality_constraint()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @variable(model, y[1:3], InfiniteLogical(t))
    
    LCR = DP.LogicalConstraintRef{InfiniteModel}
    @test @constraint(model, y in Exactly(1)) isa LCR
    @test @constraint(model, y in AtLeast(1)) isa LCR
    @test @constraint(model, y in AtMost(2)) isa LCR
end

function test_add_logical_constraint()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @variable(model, y[1:2], InfiniteLogical(t))
    
    LCR = DP.LogicalConstraintRef{InfiniteModel}
    @test @constraint(model, y[1] ∨ y[2] := true) isa LCR
    @test @constraint(model, y[1] ∧ y[2] := true) isa LCR
    @test @constraint(model, y[1] ⟹ y[2] := true) isa LCR
end

function test_add_constraint_single_logical_error()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @variable(model, y, InfiniteLogical(t))
    
    c = JuMP.ScalarConstraint(y, MOI.EqualTo(true))
    @test_throws ErrorException JuMP.add_constraint(model, c, "")
end

function test_add_constraint_affine_logical_error()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @variable(model, y[1:2], InfiniteLogical(t))

    aff_expr = 1.0 * y[1] + 1.0 * y[2]
    c = JuMP.ScalarConstraint(aff_expr, MOI.EqualTo(1.0))
    @test_throws ErrorException JuMP.add_constraint(model, c, "")
end

function test_add_constraint_quad_logical_error()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @variable(model, y[1:2], InfiniteLogical(t))
    
    quad_expr = 1.0 * y[1] * y[2]
    c = JuMP.ScalarConstraint(quad_expr, MOI.EqualTo(1.0))
    @test_throws ErrorException JuMP.add_constraint(model, c, "")
end

function test_logical_value()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    @infinite_parameter(model, t ∈ [0, 1], num_supports = 10)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, y[1:2], InfiniteLogical(t))
    
    @constraint(model, x >= 5, Disjunct(y[1]))
    @constraint(model, x <= 5, Disjunct(y[2]))
    @disjunction(model, [y[1], y[2]])
    
    @objective(model, Min, 𝔼(x, t))
    
    optimize!(model, gdp_method = Hull())
    
    val = value(y[2])
    @test eltype(val) == Bool
end

# _collect_parameters on model with no infinite parameters.
# Covers ext line 508.
function test__collect_parameters_no_params()
    model = InfiniteGDPModel()
    @test_throws ErrorException IDP._collect_parameters(model)
end

# MBM with finite + integer variables in InfiniteModel. Covers
# copy_model_with_constraints (finite var, set_integer),
# and _build_flat_map line 252 (finite var path).
function test_mbm_finite_and_integer_var()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    @infinite_parameter(model, t ∈ [0, 1], num_supports = 10)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, 0 <= w <= 5, Int)
    @variable(model, Y[1:2], InfiniteLogical(t))
    @constraint(model, x + w >= 5, Disjunct(Y[1]))
    @constraint(model, x + w <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)
    @objective(model, Min, ∫(x, t) + w)
    @test optimize!(model,
        gdp_method = MBM(HiGHS.Optimizer)) isa Nothing
    @test termination_status(model) in
        [MOI.OPTIMAL, MOI.LOCALLY_SOLVED]
end

function test_mbm_infinite_simple()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)

    @infinite_parameter(model, t ∈ [0, 1], num_supports = 10)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))

    @constraint(model, x >= 5, Disjunct(Y[1]))
    @constraint(model, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)

    @objective(model, Min, ∫(x, t))

    @test optimize!(model, gdp_method = MBM(HiGHS.Optimizer)) isa Nothing
    @test termination_status(model) in
        [MOI.OPTIMAL, MOI.LOCALLY_SOLVED]
    # x=0 with disjunct 2 active (x <= 3) gives min
    @test objective_value(model) ≈ 0.0 atol = 0.1
end

function test_mbm_infinite_param_dependent()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)

    @infinite_parameter(model, t ∈ [0, 1], num_supports = 20)
    @variable(model, -10 <= x <= 10, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))

    # Parameter-dependent constraints:
    # Disjunct 1: x(t) <= 2*t
    # Disjunct 2: x(t) >= 1 - t
    @parameter_function(model, f1 == t -> 2*t)
    @parameter_function(model, f2 == t -> 1 - t)
    @constraint(model, x <= f1, Disjunct(Y[1]))
    @constraint(model, x >= f2, Disjunct(Y[2]))
    @disjunction(model, Y)

    @objective(model, Min, ∫(x, t))

    @test optimize!(model, gdp_method = MBM(HiGHS.Optimizer)) isa Nothing
    @test termination_status(model) in
        [MOI.OPTIMAL, MOI.LOCALLY_SOLVED]
end

function test_mbm_vs_bigm_infinite()
    # Compare MBM and BigM: should give same
    # feasible set and optimal value.
    for method_pair in [
        (BigM(100), MBM(HiGHS.Optimizer))
    ]
        model1 = InfiniteGDPModel(HiGHS.Optimizer)
        set_silent(model1)
        @infinite_parameter(model1, t ∈ [0, 1], num_supports = 10)
        @variable(model1, 0 <= x1 <= 10, Infinite(t))
        @variable(model1, Y1[1:2], InfiniteLogical(t))
        @constraint(model1, x1 >= 5, Disjunct(Y1[1]))
        @constraint(model1, x1 <= 3, Disjunct(Y1[2]))
        @disjunction(model1, Y1)
        @objective(model1, Min, ∫(x1, t))
        optimize!(model1, gdp_method = method_pair[1])
        obj1 = objective_value(model1)

        model2 = InfiniteGDPModel(HiGHS.Optimizer)
        set_silent(model2)
        @infinite_parameter(model2, t2 ∈ [0, 1], num_supports = 10)
        @variable(model2, 0 <= x2 <= 10, Infinite(t2))
        @variable(model2, Y2[1:2], InfiniteLogical(t2))
        @constraint(model2, x2 >= 5, Disjunct(Y2[1]))
        @constraint(model2, x2 <= 3, Disjunct(Y2[2]))
        @disjunction(model2, Y2)
        @objective(model2, Min, ∫(x2, t2))
        optimize!(model2, gdp_method = method_pair[2])
        obj2 = objective_value(model2)

        @test obj1 ≈ obj2 atol = 0.5
    end
end

function test_methods()
    I = 1:3
    J = 1:6
    period_bounds = collect(0:1:6)
    expected_obj = 4.504541662743021
    expected_z = -1.3634301575859131
    tol = 0.1

    # Use Juniper for MIQP support (HiGHS cannot solve MIQP)
    ipopt = optimizer_with_attributes(Ipopt.Optimizer, 
        "print_level" => 0, "sb" => "yes"
    )
    optimizer = optimizer_with_attributes(Juniper.Optimizer, "nl_solver" => ipopt)
    model = InfiniteGDPModel(optimizer)
    set_attribute(model, MOI.Silent(), true)

    @infinite_parameter(
        model, τ[j in J] in [period_bounds[j], period_bounds[j+1]], 
        num_supports = 5, independent = true, container = Array
    )
    @variable(model, -5 ≤ y[j in J] ≤ 5, Infinite(τ[j]), container = Array)
    @variable(model, -4 ≤ z ≤ 4)
    @objective(model, Min, 10 * sum(∫(y[j]^2, τ[j]) for j in J))

    @constraint(model, y[1](0) == 1)
    @constraint(model, [j = 2:6], y[j](period_bounds[j]) == y[j-1](period_bounds[j]))

    @variable(model, W[i = I, j = J], Logical)
    @constraint(model, [j in J], ∂(y[j], τ[j]) == -2*τ[j] + 0.3*z - 20*y[j], Disjunct(W[1, j]))
    @constraint(model, [j in J], ∂(y[j], τ[j]) == -2*z + 0.4*τ[j] - 4, Disjunct(W[2, j]))
    @constraint(model, [j in J], ∂(y[j], τ[j]) == 2*z + 4*(τ[j] - y[j] - 1), Disjunct(W[3, j]))
    @disjunction(model, [j in J], W[:, j])

    for j in J
        set_upper_bound(∂(y[j], τ[j]), 100)
        set_lower_bound(∂(y[j], τ[j]), -100)
    end

    @test optimize!(model, gdp_method = BigM()) isa Nothing
    @test objective_value(model) ≈ expected_obj atol=tol
    @test value(z) ≈ expected_z atol=tol

    @test optimize!(model, gdp_method = Hull()) isa Nothing
    @test objective_value(model) ≈ expected_obj atol=tol
    @test value(z) ≈ expected_z atol=tol

    @test optimize!(model, gdp_method = PSplit(3, model)) isa Nothing
    @test objective_value(model) ≈ expected_obj atol=tol
    @test value(z) ≈ expected_z atol=tol
end

function test_mbm_with_derivatives()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)

    @infinite_parameter(model, t ∈ [0, 1], num_supports = 10)
    @variable(model, -5 <= x <= 5, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))

    @constraint(model, ∂(x, t) >= 1, Disjunct(Y[1]))
    @constraint(model, ∂(x, t) <= -1, Disjunct(Y[2]))
    @disjunction(model, Y)

    set_upper_bound(∂(x, t), 10)
    set_lower_bound(∂(x, t), -10)

    @objective(model, Min, ∫(x^2, t))

    juniper = JuMP.optimizer_with_attributes(
        Juniper.Optimizer,
        "nl_solver" => JuMP.optimizer_with_attributes(
            Ipopt.Optimizer, "print_level" => 0),
        "log_levels" => []
    )
    set_optimizer(model, juniper)
    @test optimize!(model, gdp_method = MBM(juniper)) isa Nothing
    @test termination_status(model) in
        [MOI.OPTIMAL, MOI.LOCALLY_SOLVED,
         MOI.ALMOST_LOCALLY_SOLVED]
end

function test_CuttingPlanes_infinite_simple()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)

    @infinite_parameter(model, t ∈ [0, 1], num_supports = 10)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))

    @constraint(model, x >= 5, Disjunct(Y[1]))
    @constraint(model, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)

    @objective(model, Min, ∫(x, t))

    # Should not throw
    @test optimize!(model,
        gdp_method = CuttingPlanes(
            HiGHS.Optimizer; max_iter = 5)
    ) isa Nothing
    @test termination_status(model) in
        [MOI.OPTIMAL, MOI.LOCALLY_SOLVED]
end

function test_CuttingPlanes_infinite_two_disj()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)

    @infinite_parameter(model, t ∈ [0, 1], num_supports = 10)
    @variable(model, 0 <= x[1:2] <= 10, Infinite(t))
    @variable(model, W1[1:2], InfiniteLogical(t))
    @variable(model, W2[1:2], InfiniteLogical(t))

    @constraint(model, x[1] >= 2, Disjunct(W1[1]))
    @constraint(model, x[1] <= 1, Disjunct(W1[2]))
    @disjunction(model, W1)

    @constraint(model, x[2] >= 3, Disjunct(W2[1]))
    @constraint(model, x[2] <= 2, Disjunct(W2[2]))
    @disjunction(model, W2)

    @objective(model, Min, ∫(x[1] + x[2], t))

    # Compare cutting planes vs BigM
    optimize!(model,
        gdp_method = CuttingPlanes(
            HiGHS.Optimizer; max_iter = 10)
    )
    cp_obj = objective_value(model)

    model2 = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model2)
    @infinite_parameter(model2, t2 ∈ [0, 1], num_supports = 10)
    @variable(model2, 0 <= x2[1:2] <= 10, Infinite(t2))
    @variable(model2, V1[1:2], InfiniteLogical(t2))
    @variable(model2, V2[1:2], InfiniteLogical(t2))
    @constraint(model2, x2[1] >= 2, Disjunct(V1[1]))
    @constraint(model2, x2[1] <= 1, Disjunct(V1[2]))
    @disjunction(model2, V1)
    @constraint(model2, x2[2] >= 3, Disjunct(V2[1]))
    @constraint(model2, x2[2] <= 2, Disjunct(V2[2]))
    @disjunction(model2, V2)
    @objective(model2, Min, ∫(x2[1] + x2[2], t2))
    optimize!(model2, gdp_method = BigM())
    bigm_obj = objective_value(model2)

    @test cp_obj ≈ bigm_obj atol = 1.0
end



function test_CuttingPlanes_with_cuts()
    # Maximization with single-constraint disjuncts where Hull
    # is strictly tighter than BigM. BigM allows x+y up to
    # variable bounds (20), Hull limits to max(5,8)=8. This
    # forces cuts. Finite var w exercises isempty(vprefs)
    # branch in add_original_model_cut (line 779).
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    @infinite_parameter(model, t ∈ [0, 1], num_supports = 10)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, 0 <= y <= 10, Infinite(t))
    @variable(model, 0 <= w <= 10)
    @variable(model, Y[1:2], InfiniteLogical(t))
    @constraint(model, x + y <= 5, Disjunct(Y[1]))
    @constraint(model, x + y <= 8, Disjunct(Y[2]))
    @disjunction(model, Y)
    @objective(model, Max, ∫(x + y, t) + w)
    cutting_planes = CuttingPlanes(HiGHS.Optimizer;
        max_iter = 30, seperation_tolerance = 1e-6)
    @test optimize!(model, gdp_method = cutting_planes) isa Nothing
    @test termination_status(model) in
        [MOI.OPTIMAL, MOI.LOCALLY_SOLVED]
end

function test_CuttingPlanes_multiparameter()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)

    @infinite_parameter(model, t ∈ [0, 1], num_supports = 5)
    @infinite_parameter(model, s ∈ [0, 2], num_supports = 4)
    @variable(model, 0 <= x <= 10, Infinite(t, s))
    @variable(model, Y[1:2], InfiniteLogical(t, s))

    @constraint(model, x >= 5, Disjunct(Y[1]))
    @constraint(model, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)

    @objective(model, Min, ∫(∫(x, t), s))

    # Should not throw
    @test optimize!(model,
        gdp_method = CuttingPlanes(
            HiGHS.Optimizer; max_iter = 5)
    ) isa Nothing
    @test termination_status(model) in
        [MOI.OPTIMAL, MOI.LOCALLY_SOLVED]
end

@testset "InfiniteDisjunctiveProgramming" begin

    @testset "Model" begin
        test_infinite_gdp_model_creation()
    end

    @testset "all_variables" begin
        test_all_variables_infiniteopt()
    end

    @testset "Variables" begin
        test_infinite_logical()
        test__is_parameter()
        test__is_parameter_concrete_dispatches()
        test_requires_disaggregation()
        test_variable_properties_infiniteopt()
        test_variable_properties_from_expr()
        test_variable_properties_from_quad_expr()
        test_variable_properties_from_nonlinear_expr()
        test_variable_properties_from_vector()
    end

    @testset "Constraints" begin
        test_add_cardinality_constraint()
        test_add_logical_constraint()
    end

    @testset "JuMP Overloads" begin
        test_logical_value()
        test_add_constraint_single_logical_error()
        test_add_constraint_affine_logical_error()
        test_add_constraint_quad_logical_error()
    end

    @testset "Methods" begin
        test_get_constant()
        test_disaggregate_expression_infiniteopt()
        test_disaggregate_quad_expression_infiniteopt()
    end

    @testset "Internal Helpers" begin
        test__collect_parameters_no_params()
    end

    @testset "MBM" begin
        test_mbm_finite_and_integer_var()
        test_mbm_infinite_simple()
        test_mbm_infinite_param_dependent()
        test_mbm_vs_bigm_infinite()
        test_mbm_with_derivatives()
    end

    @testset "Integration" begin
        test_infiniteopt_extension()
        test_methods()
    end

    @testset "Cutting Planes" begin
        test_CuttingPlanes_infinite_simple()
        test_CuttingPlanes_infinite_two_disj()
        test_CuttingPlanes_with_cuts()
        test_CuttingPlanes_multiparameter()
    end


end