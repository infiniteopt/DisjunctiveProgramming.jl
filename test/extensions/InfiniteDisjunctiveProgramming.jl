using InfiniteOpt, HiGHS, Ipopt, Juniper
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

function test_unsupported_methods_error()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    @test_throws ErrorException DP.reformulate_model(model, MBM(HiGHS.Optimizer))
    @test_throws ErrorException DP.reformulate_model(model, CuttingPlanes(HiGHS.Optimizer))
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
        test_unsupported_methods_error()
    end

    @testset "Integration" begin
        test_infiniteopt_extension()
        test_methods()
    end

end