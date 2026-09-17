using InfiniteOpt, HiGHS, Ipopt, Juniper, Pajarito, Hypatia
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

function test_is_parameter()
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

# _is_parameter on unwrapped concrete dispatch types
# (DependentParameterRef, IndependentParameterRef, FiniteParameterRef,
# ParameterFunctionRef, Any fallback).
function test_is_parameter_concrete_dispatches()
    model = InfiniteGDPModel()
    # Scalar + `independent = true` array both give IndependentParameterRef;
    # a default array parameter gives DependentParameterRef.
    @infinite_parameter(model, t ∈ [0, 1])
    @infinite_parameter(model, s[1:2] ∈ [0, 1], independent = true)
    @infinite_parameter(model, q[1:2] ∈ [0, 1])
    @finite_parameter(model, p == 1.0)
    @variable(model, x, Infinite(t))
    @parameter_function(model, pf == t -> 2*t)
    dvr = InfiniteOpt.dispatch_variable_ref
    # Verify each ref hits the intended dispatch.
    @test dvr(t) isa InfiniteOpt.IndependentParameterRef
    @test dvr(s[1]) isa InfiniteOpt.IndependentParameterRef
    @test dvr(q[1]) isa InfiniteOpt.DependentParameterRef
    @test dvr(p) isa InfiniteOpt.FiniteParameterRef
    @test dvr(pf) isa InfiniteOpt.ParameterFunctionRef
    @test IDP._is_parameter(dvr(t)) == true
    @test IDP._is_parameter(dvr(s[1])) == true
    @test IDP._is_parameter(dvr(q[1])) == true
    @test IDP._is_parameter(dvr(p)) == true
    @test IDP._is_parameter(dvr(pf)) == true
    @test IDP._is_parameter(dvr(x)) == false    # Any fallback
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

# Parameter refs in disjunct constraints answer the standard JuMP
# bound queries (InfiniteOpt bound support): finite parameters their
# value, infinite parameters their domain bounds, parameter functions
# any user-declared bounds. The base set_variable_bound_info methods
# handle them like variables, so no extension overrides are needed.
function test_parameter_bound_info()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t in [0, 1])
    @finite_parameter(model, p == 2.0)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, y, Infinite(t))
    @parameter_function(model, pf == t -> 2t - 1)
    set_lower_bound(pf, -1)
    set_upper_bound(pf, 1)
    @parameter_function(model, pf2 == t -> sin(t))
    @test DP.set_variable_bound_info(pf, BigM()) == (-1.0, 1.0)
    @test DP.set_variable_bound_info(p, BigM()) == (2.0, 2.0)
    @test DP.set_variable_bound_info(t, BigM()) == (0.0, 1.0)
    @test DP.set_variable_bound_info(x, BigM()) == (0.0, 10.0)
    @test DP.set_variable_bound_info(y, BigM()) == (-Inf, Inf)
    # parameter functions without declared bounds fall back
    @test DP.set_variable_bound_info(pf2, BigM()) == (-Inf, Inf)
    # Hull and PSplit clamp the bounds to include 0
    @test DP.set_variable_bound_info(pf, Hull()) == (-1.0, 1.0)
    @test DP.set_variable_bound_info(t, Hull()) == (0.0, 1.0)
    @test DP.set_variable_bound_info(p, Hull()) == (0.0, 2.0)
    @test DP.set_variable_bound_info(x, Hull()) == (0.0, 10.0)
    @test DP.set_variable_bound_info(p, PSplit([[x]])) == (0.0, 2.0)
    @test_throws ErrorException DP.set_variable_bound_info(y, Hull())
    @test_throws ErrorException DP.set_variable_bound_info(pf2, Hull())
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

function test_disaggregate_expression_parameter()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
    @finite_parameter(model, p == 2.0)
    @parameter_function(model, pf == t -> 2t)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, w, Bin)
    @variable(model, z, InfiniteLogical(t))
    bvref = DP._indicator_to_binary(model)[z]
    method = DP._Hull(Hull(), Set([x]))
    DP._variable_bounds(model)[x] = DP.set_variable_bound_info(x, Hull())
    DP._disaggregate_variables(model, z, Set([x]), method)
    dvref = method.disjunct_variables[x, bvref]
    # parameters scale with the indicator, variables map through
    @test isequal_canonical(
        DP.disaggregate_expression(model, t, bvref, method), t * bvref)
    @test isequal_canonical(
        DP.disaggregate_expression(model, p, bvref, method), p * bvref)
    @test isequal_canonical(
        DP.disaggregate_expression(model, pf, bvref, method), pf * bvref)
    @test isequal(DP.disaggregate_expression(model, x, bvref, method), dvref)
    @test isequal(DP.disaggregate_expression(model, w, bvref, method), w)
end

function test_split_quad_terms_infinite()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1])
    @parameter_function(model, pf == t -> 2t)
    @variable(model, x, Infinite(t))
    quad = @expression(model, x^2 + t*x + t*pf + 3x + 2)
    quad_part, affine_part = DP._split_quad_terms(quad)
    @test isequal_canonical(quad_part, @expression(model, x^2))
    @test isequal_canonical(
        affine_part, @expression(model, t*x + t*pf + 3x + 2))
end

function test_epsilon_quad_hull_parameter()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
    @parameter_function(model, pf == t -> 2t)
    @variable(model, -2 <= x <= 3, Infinite(t))
    @variable(model, z, InfiniteLogical(t))
    @constraint(model, con, x^2 + pf*x <= 1, Disjunct(z))
    bvref = DP._indicator_to_binary(model)[z]
    ϵ = 1e-3
    method = DP._Hull(Hull(ϵ), Set([x]))
    DP._variable_bounds(model)[x] = DP.set_variable_bound_info(x, Hull())
    DP._disaggregate_variables(model, z, Set([x]), method)
    x_z = method.disjunct_variables[x, bvref]
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), bvref, method)
    @test length(ref) == 1
    # pf*ν stays undivided, ν² is ε-divided, the set value scales with y
    vals1 = Dict(x_z => 2.0, pf => 0.5, bvref => 1.0)
    @test _eval_at(v -> vals1[v], ref[1].func) ≈ 4.0 + 1.0 - 1.0
    vals2 = Dict(x_z => 1.0, pf => 0.5, bvref => 0.5)
    expected2 = 1.0 / ((1 - ϵ)*0.5 + ϵ) + 0.5 - 0.5
    @test _eval_at(v -> vals2[v], ref[1].func) ≈ expected2
end

# evaluate an expression at a point (InfiniteOpt lacks value(f, vref))
_eval_at(f, x::Number) = x
_eval_at(f, v::GeneralVariableRef) = f(v)
function _eval_at(f, e::JuMP.GenericAffExpr)
    return e.constant + sum(c * f(v) for (v, c) in e.terms; init = 0.0)
end
function _eval_at(f, e::JuMP.GenericQuadExpr)
    return _eval_at(f, e.aff) +
        sum(c * f(p.a) * f(p.b) for (p, c) in e.terms; init = 0.0)
end
function _eval_at(f, e::JuMP.GenericNonlinearExpr)
    return getfield(Base, e.head)((_eval_at(f, a) for a in e.args)...)
end

function test_gehr_infinite()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
    @variable(model, -2 <= x <= 3, Infinite(t))
    @variable(model, z, InfiniteLogical(t))
    @constraint(model, con, x^2 + t*x <= 1, Disjunct(z))
    bvref = DP._indicator_to_binary(model)[z]
    method = DP._Hull(Hull(quadratic = :gehr), Set([x]))
    DP._variable_bounds(model)[x] = DP.set_variable_bound_info(x, Hull())
    DP._disaggregate_variables(model, z, Set([x]), method)
    x_z = method.disjunct_variables[x, bvref]
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), bvref, method)
    @test length(ref) == 1
    @test ref[1].set == MOI.LessThan(0)
    # GEHR must give ν² + t*ν*y - y² (parameter terms scale once with y)
    vals1 = Dict(x_z => 2.0, t => 0.5, bvref => 1.0)
    @test _eval_at(v -> vals1[v], ref[1].func) ≈ 4.0 + 1.0 - 1.0
    vals2 = Dict(x_z => 1.0, t => 1.0, bvref => 0.5)
    @test _eval_at(v -> vals2[v], ref[1].func) ≈ 1.0 + 0.5 - 0.25
end

function test_cehr_infinite()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
    @parameter_function(model, pf == t -> 2t)
    @variable(model, -2 <= x <= 3, Infinite(t))
    @variable(model, z, InfiniteLogical(t))
    @constraint(model, con, x^2 + 2x - pf <= 0, Disjunct(z))
    bvref = DP._indicator_to_binary(model)[z]
    method = DP._Hull(Hull(quadratic = :exact), Set([x]))
    DP._variable_bounds(model)[x] = DP.set_variable_bound_info(x, Hull())
    DP._disaggregate_variables(model, z, Set([x]), method)
    x_z = method.disjunct_variables[x, bvref]
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), bvref, method)
    @test length(ref) == 2
    tvars = filter(v -> startswith(name(v), "t_cehr"),
                   DP._reformulation_variables(model))
    @test length(tvars) == 1
    tvref = only(tvars)
    # the epigraph variable is infinite over the constraint's parameter
    @test isequal(parameter_refs(tvref), (t,))
    @test lower_bound(tvref) == 0
    @test isequal_canonical(ref[1].func, x_z^2 - tvref*bvref)
    @test ref[1].set == MOI.LessThan(0.0)
    @test isequal_canonical(ref[2].func, tvref + 2*x_z - pf*bvref)
    @test ref[2].set == MOI.LessThan(0.0)
end

function test_cehr_conic_infinite()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
    @parameter_function(model, pf == t -> 2t)
    @variable(model, -2 <= x <= 3, Infinite(t))
    @variable(model, z, InfiniteLogical(t))
    @constraint(model, con, x^2 + 2x - pf <= 0, Disjunct(z))
    bvref = DP._indicator_to_binary(model)[z]
    method = DP._Hull(Hull(quadratic = :cehr_conic), Set([x]))
    DP._variable_bounds(model)[x] = DP.set_variable_bound_info(x, Hull())
    DP._disaggregate_variables(model, z, Set([x]), method)
    x_z = method.disjunct_variables[x, bvref]
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), bvref, method)
    @test length(ref) == 2
    tvref = only(filter(v -> startswith(name(v), "t_cehr"),
                        DP._reformulation_variables(model)))
    @test isequal(parameter_refs(tvref), (t,))
    @test ref[1].set == MOI.RotatedSecondOrderCone(3)
    @test isequal_canonical(ref[1].func[1], 0.5 * tvref)
    @test isequal_canonical(ref[1].func[2], 1.0 * bvref)
    @test abs(coefficient(ref[1].func[3], x_z)) ≈ 1.0
    @test isequal_canonical(ref[2].func, tvref + 2*x_z - pf*bvref)
    @test ref[2].set == MOI.LessThan(0.0)
end

function test_cehr_epigraph_finite()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
    @variable(model, -2 <= v <= 3)
    @variable(model, z, Logical)
    @constraint(model, con, v^2 + 2v <= 1, Disjunct(z))
    bvref = DP._indicator_to_binary(model)[z]
    method = DP._Hull(Hull(quadratic = :exact), Set([v]))
    DP._variable_bounds(model)[v] = DP.set_variable_bound_info(v, Hull())
    DP._disaggregate_variables(model, z, Set([v]), method)
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), bvref, method)
    @test length(ref) == 2
    tvref = only(filter(v -> startswith(name(v), "t_cehr"),
                        DP._reformulation_variables(model)))
    # a purely finite constraint gets a finite epigraph variable
    @test isempty(parameter_refs(tvref))
end

function test_conic_hull_infinite()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
    @parameter_function(model, pf == t -> 5t)
    @variable(model, -10 <= x <= 10, Infinite(t))
    @variable(model, -10 <= w <= 10, Infinite(t))
    @variable(model, z, InfiniteLogical(t))
    @constraint(model, con, [1, x - pf, w] in SecondOrderCone(), Disjunct(z))
    @constraint(model, con2, [pf, x, w] in SecondOrderCone(), Disjunct(z))
    bvref = DP._indicator_to_binary(model)[z]
    method = DP._Hull(Hull(), Set([x, w]))
    for v in (x, w)
        DP._variable_bounds(model)[v] = DP.set_variable_bound_info(v, Hull())
    end
    DP._disaggregate_variables(model, z, Set([x, w]), method)
    x_z = method.disjunct_variables[x, bvref]
    w_z = method.disjunct_variables[w, bvref]
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), bvref, method)
    @test length(ref) == 1
    @test ref[1].set == MOI.SecondOrderCone(3)
    T = eltype(ref[1].func)
    @test isequal_canonical(ref[1].func[1], convert(T, 1 * bvref))
    @test isequal_canonical(ref[1].func[2], convert(T, x_z - pf*bvref))
    @test isequal_canonical(ref[1].func[3], convert(T, 1 * w_z))
    # bare parameter rows scale with the indicator too
    ref2 = reformulate_disjunct_constraint(
        model, constraint_object(con2), bvref, method)
    T2 = eltype(ref2[1].func)
    @test isequal_canonical(ref2[1].func[1], convert(T2, pf * bvref))
    @test isequal_canonical(ref2[1].func[2], convert(T2, 1 * x_z))
end

function test_conic_all_cones_infinite()
    cones = [
        (x -> [1, x[1], x[2]], SecondOrderCone(), MOI.SecondOrderCone(3)),
        (x -> [1, x[1], x[2]], RotatedSecondOrderCone(),
         MOI.RotatedSecondOrderCone(3)),
        (x -> [x[1], 1, x[2]], MOI.ExponentialCone(), MOI.ExponentialCone()),
        (x -> [x[1], 1, x[2]], MOI.PowerCone(0.5), MOI.PowerCone(0.5)),
    ]
    for (rows, set, moi_set) in cones, meth in (Hull(), BigM(100))
        model = InfiniteGDPModel()
        @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
        @variable(model, -10 <= x <= 10, Infinite(t))
        @variable(model, -10 <= w <= 10, Infinite(t))
        @parameter_function(model, pf == t -> 1 + t)
        set_lower_bound(pf, 1)
        set_upper_bound(pf, 2)
        @variable(model, Y[1:2], InfiniteLogical(t))
        @constraint(model, rows([x - pf, w]) in set, Disjunct(Y[1]))
        @constraint(model, rows([x, w]) in set, Disjunct(Y[2]))
        @disjunction(model, Y)
        DP.reformulate_model(model, meth)
        sets = [constraint_object(c).set
                for c in DP._reformulation_constraints(model)]
        @test count(==(moi_set), sets) == 2
        InfiniteOpt.build_transformation_backend!(model)
        @test num_variables(InfiniteOpt.transformation_model(model)) > 0
    end
end

function test_conic_constant_row_infinite()
    # a constant row in a zero-direction slot keeps no variables under
    # BigM and transcribes to a number; InfiniteOpt must promote the
    # row vector to a common type (fork transcription fix)
    for meth in (Hull(), BigM(100))
        model = InfiniteGDPModel()
        @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
        @variable(model, -10 <= x <= 10, Infinite(t))
        @variable(model, 0 <= u <= 10, Infinite(t))
        @variable(model, Y[1:2], InfiniteLogical(t))
        @constraint(model, [u, x, 3] in SecondOrderCone(), Disjunct(Y[1]))
        @constraint(model, [u, x - 5, 3] in SecondOrderCone(),
                    Disjunct(Y[2]))
        @disjunction(model, Y)
        DP.reformulate_model(model, meth)
        InfiniteOpt.build_transformation_backend!(model)
        @test num_variables(InfiniteOpt.transformation_model(model)) > 0
    end
end

function test_conic_bigm_infinite()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
    @parameter_function(model, pf == t -> 5t)
    @variable(model, -10 <= x <= 10, Infinite(t))
    @variable(model, -10 <= w <= 10, Infinite(t))
    @variable(model, z, InfiniteLogical(t))
    @constraint(model, con, [1, x - pf, w] in SecondOrderCone(), Disjunct(z))
    bvref = DP._indicator_to_binary(model)[z]
    ref = reformulate_disjunct_constraint(
        model, constraint_object(con), bvref, BigM(100))
    @test length(ref) == 1
    @test ref[1].set == MOI.SecondOrderCone(3)
    @test isequal_canonical(ref[1].func[1], 1 + 100*(1 - bvref))
    @test isequal_canonical(ref[1].func[2], x - pf + 0*bvref)
    @test isequal_canonical(ref[1].func[3], 1.0*w + 0*bvref)
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

# raw_M against an InfiniteModel where M is constant across supports.
# Setup: x(t) ∈ [0, 10], disj1: x ≥ 5, disj2: x ≤ 3.
# For disj1 slack r(x) = 5 - x maximized over disj2's region x ∈ [0, 3]:
# max(5 - x) = 5 at x = 0. Same at every support ⇒ scalar M = 5.
function test_raw_M_infinite_scalar()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t ∈ [0, 1], num_supports = 5)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))
    @constraint(model, con, x >= 5, Disjunct(Y[1]))
    @constraint(model, con2, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)
    mbm = DP._MBM(MBM(HiGHS.Optimizer), model)
    sub = DP.copy_model_with_constraints(
        model, DP.DisjunctConstraintRef[con2], mbm)
    obj = DP.prepare_max_M_objective(
        model, JuMP.constraint_object(con), sub)
    @test length(InfiniteOpt.parameter_refs(obj)) == 1
    @test DP.raw_M(sub, obj, mbm) == 5.0
end

# raw_M with a support-varying M. Setup: x(t) ∈ [0, 10], disj1: x ≤ 2t,
# disj2: x ≥ 0.5. Slack r(x) = x - 2t maximized over x ∈ [0.5, 10]:
# max(x - 2t) = 10 - 2t. Varies with t ⇒ raw_M returns a pfunc whose
# raw values at supports are max-of-cell upper bounds for 10 - 2t.
function test_raw_M_infinite_param_function()
    model = InfiniteGDPModel()
    supports = [0.0, 0.25, 0.5, 0.75, 1.0]
    @infinite_parameter(model, t ∈ [0, 1], supports = supports)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))
    @parameter_function(model, f == t -> 2*t)
    @constraint(model, con, x <= f, Disjunct(Y[1]))
    @constraint(model, con2, x >= 0.5, Disjunct(Y[2]))
    @disjunction(model, Y)
    mbm = DP._MBM(MBM(HiGHS.Optimizer), model)
    sub = DP.copy_model_with_constraints(
        model, DP.DisjunctConstraintRef[con2], mbm)
    obj = DP.prepare_max_M_objective(
        model, JuMP.constraint_object(con), sub)
    M = DP.raw_M(sub, obj, mbm)
    @test M isa InfiniteOpt.GeneralVariableRef
    raw_fn = InfiniteOpt.raw_function(M)
    # max-of-corners is conservative: raw_fn(t) ≥ 10 - 2t at supports.
    for t_val in supports
        @test raw_fn(t_val) >= 10.0 - 2*t_val - 1e-6
    end
end

# Piecewise-constant max-of-corners: returns the maximum value over
# the 2^n corners of the cell containing the query.
function test_interpolate()
    grid1 = [0.0, 1.0, 2.0, 3.0]
    vals1 = [10.0, 20.0, 40.0, 50.0]
    f = IDP._interpolate((grid1,), vals1)
    # At grid points: max over the cell to the right (or last cell).
    @test f(0.0) == 20.0   # max(vals[1], vals[2])
    @test f(1.0) == 40.0   # max(vals[2], vals[3])
    @test f(3.0) == 50.0   # last cell: max(vals[3], vals[4])
    # Between grid points: max of the surrounding two values.
    @test f(0.5) == 20.0
    @test f(1.5) == 40.0
    @test f(2.25) == 50.0
    # Out-of-range clamps to the boundary cell.
    @test f(-1.0) == 20.0
    @test f(4.0) == 50.0

    # 2D: max over the 4 surrounding corners.
    gx = [0.0, 1.0, 2.0]
    gy = [0.0, 10.0]
    vals2 = [x * y for x in gx, y in gy]   # 3x2 matrix
    g = IDP._interpolate((gx, gy), vals2)
    @test g(0.0, 0.0) == 10.0   # corners (0,0)=0, (1,0)=0, (0,10)=0, (1,10)=10
    @test g(2.0, 10.0) == 20.0  # last cell, max corner is (2,10)=20
    @test g(0.5, 5.0) == 10.0   # corners 0,0,0,10 -> 10
    @test g(1.5, 5.0) == 20.0   # corners 0,0,10,20 -> 20
end

# extract_solution returns per-support values from the transformation
# backend. Setup: force disj 2 active (x ≤ 3), BigM-reformulate, solve
# min ∫x ⇒ x = 0 at every support.
function test_extract_solution_infinite()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    K = 4
    @infinite_parameter(model, t ∈ [0, 1], num_supports = K)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))
    @constraint(model, x >= 5, Disjunct(Y[1]))
    @constraint(model, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)
    JuMP.fix(Y[2], true)  # force disj 2 active
    @objective(model, Min, ∫(x, t))
    DP.reformulate_model(model, BigM(10.0))
    set_optimizer(model, HiGHS.Optimizer)
    set_silent(model)
    optimize!(model, ignore_optimize_hook = true)
    reform_state = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model)
    sol = DP.extract_solution(model, reform_state)
    @test haskey(sol, x)
    @test length(sol[x]) == K
    @test all(v -> isapprox(v, 0.0; atol=1e-6), sol[x])
end

# add_cut adds one pointwise-sum cut to the transformation backend and
# marks the backend ready so the next optimize! does NOT re-transcribe.
function test_add_cut_infinite()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    K = 3
    @infinite_parameter(model, t ∈ [0, 1], num_supports = K)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))
    @constraint(model, x >= 5, Disjunct(Y[1]))
    @constraint(model, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)
    DP.reformulate_model(model, BigM(10.0))
    InfiniteOpt.build_transformation_backend!(model)
    transcribed = InfiniteOpt.transformation_model(model)
    n_before = JuMP.num_constraints(transcribed;
        count_variable_in_set_constraints = false)
    rBM_sol = Dict(x => [1.0, 2.0, 3.0])
    sep_sol = Dict(x => [0.5, 1.5, 2.5])
    # add_cut reads the decision variables and weights from the CP
    # working state; restrict both to x for this isolated call
    reform_state = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model)
    reform_state.decision_vars = [x]
    reform_state.weights[x] = ones(3)
    DP.add_cut(model, reform_state, rBM_sol, sep_sol)
    n_after = JuMP.num_constraints(transcribed;
        count_variable_in_set_constraints = false)
    @test n_after == n_before + 1
    # set_transformation_backend_ready(true) — next optimize! should
    # reuse without re-transcribing (otherwise our cut would be lost)
    @test InfiniteOpt.transformation_backend_ready(model)
end

# MBM with finite + integer variables in an InfiniteModel.
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

function test_conic_methods_infinite()
    # Infinite version of the circle disjunction from test/solve.jl:
    # unit disk at the origin or at (pf(t), 0) with pf = 5t; minimizing
    # the integral of x picks the origin disk with x(t) = -1.
    oa = optimizer_with_attributes(HiGHS.Optimizer, MOI.Silent() => true)
    cs = optimizer_with_attributes(Hypatia.Optimizer, MOI.Silent() => true)
    paj = optimizer_with_attributes(Pajarito.Optimizer,
        "oa_solver" => oa, "conic_solver" => cs, "verbose" => false)
    for meth in (BigM(100), Hull())
        model = InfiniteGDPModel(paj)
        set_attribute(model, MOI.Silent(), true)
        @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
        @variable(model, -10 <= x <= 10, Infinite(t))
        @variable(model, -10 <= w <= 10, Infinite(t))
        @parameter_function(model, pf == t -> 5t)
        set_lower_bound(pf, 0)
        set_upper_bound(pf, 5)
        @variable(model, Y[1:2], InfiniteLogical(t))
        @objective(model, Min, ∫(x, t))
        @constraint(model, [1, x, w] in SecondOrderCone(), Disjunct(Y[1]))
        @constraint(model, [1, x - pf, w] in SecondOrderCone(), Disjunct(Y[2]))
        @disjunction(model, Y)
        @test optimize!(model, gdp_method = meth) isa Nothing
        @test termination_status(model) == MOI.OPTIMAL
        @test objective_value(model) ≈ -1 atol = 1e-3
        @test all(isapprox.(value(x), -1, atol = 1e-3))
    end
end

function test_exact_quad_methods_infinite()
    # Disk at (pf(t), 0) with pf = 4t - 2, or the unit disk at the
    # origin: the optimal x(t) = min(4t - 3, -1) switches disjunct at
    # t = 0.5. All methods must agree on the objective.
    ipopt = optimizer_with_attributes(Ipopt.Optimizer,
        "print_level" => 0, "sb" => "yes")
    juniper = optimizer_with_attributes(Juniper.Optimizer,
        "nl_solver" => ipopt)
    objectives = Float64[]
    for meth in (BigM(100), Hull(), Hull(quadratic = :exact),
                 Hull(quadratic = :gehr))
        model = InfiniteGDPModel(juniper)
        set_attribute(model, MOI.Silent(), true)
        @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
        @variable(model, -10 <= x <= 10, Infinite(t))
        @variable(model, -10 <= w <= 10, Infinite(t))
        @parameter_function(model, pf == t -> 4t - 2)
        set_lower_bound(pf, -2)
        set_upper_bound(pf, 2)
        @variable(model, Y[1:2], InfiniteLogical(t))
        @objective(model, Min, ∫(x, t))
        @constraint(model, (x - pf)^2 + w^2 <= 1, Disjunct(Y[1]))
        @constraint(model, x^2 + w^2 <= 1, Disjunct(Y[2]))
        @disjunction(model, Y)
        @test optimize!(model, gdp_method = meth) isa Nothing
        @test termination_status(model) in (MOI.OPTIMAL, MOI.LOCALLY_SOLVED)
        push!(objectives, objective_value(model))
        @test value(x) ≈ [-3.0, -1.0, -1.0] atol = 1e-3
    end
    @test all(isapprox.(objectives, objectives[1], atol = 1e-3))
end

function test_cehr_conic_methods_infinite()
    # Same switching geometry without a pf² term so the CEHR link stays
    # quadratic and the transcription is a true MISOCP for Pajarito:
    # x² - 2pf⋅x + w² <= 1 is the disk at (pf, 0) with radius √(1+pf²).
    oa = optimizer_with_attributes(HiGHS.Optimizer, MOI.Silent() => true)
    cs = optimizer_with_attributes(Hypatia.Optimizer, MOI.Silent() => true)
    paj = optimizer_with_attributes(Pajarito.Optimizer,
        "oa_solver" => oa, "conic_solver" => cs, "verbose" => false)
    model = InfiniteGDPModel(paj)
    set_attribute(model, MOI.Silent(), true)
    @infinite_parameter(model, t ∈ [0, 1], supports = [0.0, 0.5, 1.0])
    @variable(model, -10 <= x <= 10, Infinite(t))
    @variable(model, -10 <= w <= 10, Infinite(t))
    @parameter_function(model, pf == t -> 4t - 2)
    set_lower_bound(pf, -2)
    set_upper_bound(pf, 2)
    @variable(model, Y[1:2], InfiniteLogical(t))
    @objective(model, Min, ∫(x, t))
    @constraint(model, x^2 - 2*pf*x + w^2 <= 1, Disjunct(Y[1]))
    @constraint(model, x^2 + w^2 <= 1, Disjunct(Y[2]))
    @disjunction(model, Y)
    @test optimize!(model, gdp_method = Hull(quadratic = :cehr_conic)) isa
        Nothing
    @test termination_status(model) == MOI.OPTIMAL
    expected = [min(p - sqrt(1 + p^2), -1.0) for p in (-2.0, 0.0, 2.0)]
    @test value(x) ≈ expected atol = 1e-3
end

function test_exact_quad_ground_truth()
    # Reformulate-then-transcribe must match transcribing first: fix pf
    # at each support and solve the finite GDP with the same method.
    ipopt = optimizer_with_attributes(Ipopt.Optimizer,
        "print_level" => 0, "sb" => "yes")
    juniper = optimizer_with_attributes(Juniper.Optimizer,
        "nl_solver" => ipopt)
    supports = [0.0, 0.5, 1.0]
    for meth in (Hull(quadratic = :exact), Hull(quadratic = :gehr))
        model = InfiniteGDPModel(juniper)
        set_attribute(model, MOI.Silent(), true)
        @infinite_parameter(model, t ∈ [0, 1], supports = supports)
        @variable(model, -10 <= x <= 10, Infinite(t))
        @variable(model, -10 <= w <= 10, Infinite(t))
        @parameter_function(model, pf == t -> 4t - 2)
        set_lower_bound(pf, -2)
        set_upper_bound(pf, 2)
        @variable(model, Y[1:2], InfiniteLogical(t))
        @objective(model, Min, ∫(x, t))
        @constraint(model, (x - pf)^2 + w^2 <= 1, Disjunct(Y[1]))
        @constraint(model, x^2 + w^2 <= 1, Disjunct(Y[2]))
        @disjunction(model, Y)
        optimize!(model, gdp_method = meth)
        xvals = value(x)
        for (k, s) in enumerate(supports)
            m = GDPModel(juniper)
            set_attribute(m, MOI.Silent(), true)
            pfv = 4s - 2
            @variable(m, -10 <= xs <= 10)
            @variable(m, -10 <= ws <= 10)
            @variable(m, Ys[1:2], Logical)
            @objective(m, Min, xs)
            @constraint(m, (xs - pfv)^2 + ws^2 <= 1, Disjunct(Ys[1]))
            @constraint(m, xs^2 + ws^2 <= 1, Disjunct(Ys[2]))
            @disjunction(m, Ys)
            optimize!(m, gdp_method = meth)
            @test xvals[k] ≈ value(xs) atol = 1e-3
        end
    end
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
    # variable bounds (20), Hull limits to max(5,8)=8 — this
    # forces cuts to tighten the relaxation. Finite var w exercises
    # the isempty(var_prefs) branch in add_cut.
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

# Quadrature weights: trapezoid coefficients from the objective's
# default UniTrapezoid integrals on uniform and nonuniform grids,
# unit weight for finite variables, and the model left unchanged.
function test_quadrature_weights_trapezoid()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    @infinite_parameter(model, t ∈ [0, 1], num_supports = 5)
    @infinite_parameter(model, s ∈ [0, 1], supports = [0.0, 0.1, 0.4, 1.0])
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, 0 <= y <= 10, Infinite(s))
    @variable(model, 0 <= w <= 10)
    @variable(model, Y[1:2], InfiniteLogical(t))
    @constraint(model, x >= 5, Disjunct(Y[1]))
    @constraint(model, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)
    @objective(model, Min, ∫(x, t) + ∫(y, s) + w)

    reform_state = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model)
    DP.copy_and_reformulate(
        model, reform_state.decision_vars, Hull(), reform_state)
    weights = reform_state.weights

    # UniTrapezoid, uniform grid h = 0.25: [h/2, h, h, h, h/2]
    @test weights[x] ≈ [0.125, 0.25, 0.25, 0.25, 0.125]
    # UniTrapezoid, nonuniform grid [0, 0.1, 0.4, 1.0]
    @test weights[y] ≈ [0.05, 0.2, 0.45, 0.3]
    # finite variable: unit weight
    @test weights[w] == [1.0]
    # the objective is never rewritten
    @test JuMP.objective_sense(model) == MOI.MIN_SENSE
    @test length(JuMP.objective_function(model).terms) == 3
end

# The weights match the objective's evaluation scheme, not a
# hardcoded rule: a GaussLegendre integral yields Gauss weights on
# its generated nodes and zero weight on the remaining supports.
function test_quadrature_weights_gauss()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    @infinite_parameter(model, t ∈ [0, 1], num_supports = 5)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))
    @constraint(model, x >= 5, Disjunct(Y[1]))
    @constraint(model, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)
    @objective(model, Min, ∫(x, t, eval_method = GaussLegendre()))

    reform_state = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model)
    DP.copy_and_reformulate(
        model, reform_state.decision_vars, Hull(), reform_state)
    w = reform_state.weights[x]

    @test sum(w) ≈ 1.0
    @test any(iszero, w)  # the uniform supports carry no weight
    @test length(w) > 5   # Gauss nodes were added to the grid
end

# Multi-parameter weights: the tensor weights align with
# vec(transformation_variable) via the flattened support tuples.
function test_quadrature_weights_multiparameter()
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

    reform_state = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model)
    DP.copy_and_reformulate(
        model, reform_state.decision_vars, Hull(), reform_state)
    w = reform_state.weights[x]

    @test length(w) == 20
    # total weight = measure of the domain [0,1] x [0,2]
    @test sum(w) ≈ 2.0

    # per-support alignment: w[k] = omega_t(t_k) * omega_s(s_k)
    # for the support tuple (t_k, s_k) at the same flattened index
    InfiniteOpt.build_transformation_backend!(model)
    wt = Dict(zip(InfiniteOpt.supports(t), [0.125, 0.25, 0.25, 0.25, 0.125]))
    ws = Dict(zip(InfiniteOpt.supports(s), [1/3, 2/3, 2/3, 1/3]))
    supps = vec(InfiniteOpt.supports(x))
    for k in eachindex(supps)
        @test w[k] ≈ wt[supps[k][1]] * ws[supps[k][2]]
    end
end

# No measure in the objective: a scalar interval parameter falls
# back to the default integral (trapezoid on its own supports), a
# distribution parameter to the support average (an integral would
# add quadrature nodes and misalign the weights), and a finite
# variable keeps the unit weight.
function test_quadrature_weights_default_fallbacks()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    @infinite_parameter(model, t in [0, 1], num_supports = 5)
    @infinite_parameter(model, xi ~ InfiniteOpt.Distributions.Normal(),
        num_supports = 4)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, 0 <= z <= 10, Infinite(xi))
    @variable(model, 0 <= w <= 10)
    @variable(model, Y[1:2], InfiniteLogical(t))
    @constraint(model, x >= 5, Disjunct(Y[1]))
    @constraint(model, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)
    @objective(model, Min, w + 1)

    reform_state = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model)
    DP.copy_and_reformulate(
        model, reform_state.decision_vars, Hull(), reform_state)

    @test reform_state.weights[x] ≈ [0.125, 0.25, 0.25, 0.25, 0.125]
    @test reform_state.weights[z] ≈ fill(0.25, 4)
    @test reform_state.weights[w] == [1.0]
end

# Dependent groups always get the support average: 1/N per joint
# support, aligned with the transcription, for random and interval
# domains alike.
function test_quadrature_weights_dependent_groups()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    @infinite_parameter(model, xi[1:2] ~ InfiniteOpt.Distributions.MvNormal(
        [0.0, 0.0], [1.0 0.0; 0.0 1.0]), num_supports = 4)
    @variable(model, 0 <= z <= 10, Infinite(xi))
    @variable(model, Y[1:2], InfiniteLogical(xi))
    @constraint(model, z >= 5, Disjunct(Y[1]))
    @constraint(model, z <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)

    reform_state = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model)
    DP.copy_and_reformulate(
        model, reform_state.decision_vars, Hull(), reform_state)
    @test reform_state.weights[z] ≈ fill(0.25, 4)

    model2 = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model2)
    @infinite_parameter(model2, q[1:2] in [0, 1], num_supports = 3)
    @variable(model2, 0 <= z2 <= 10, Infinite(q))
    @variable(model2, W[1:2], InfiniteLogical(q))
    @constraint(model2, z2 >= 5, Disjunct(W[1]))
    @constraint(model2, z2 <= 3, Disjunct(W[2]))
    @disjunction(model2, W)

    reform_state2 = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model2)
    DP.copy_and_reformulate(
        model2, reform_state2.decision_vars, Hull(), reform_state2)
    @test reform_state2.weights[z2] ≈ fill(1 / 3, 3)
end

# A measure over a dependent group is read off its own data rather
# than averaged: the joint supports the measure generates carry its
# coefficients, and the model's original supports carry none.
function test_quadrature_weights_dependent_group_measure()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    @infinite_parameter(model, q[1:2] in [0, 1], num_supports = 3)
    @variable(model, 0 <= z <= 10, Infinite(q))
    @variable(model, Y[1:2], InfiniteLogical(q))
    @constraint(model, z >= 5, Disjunct(Y[1]))
    @constraint(model, z <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)
    @objective(model, Min, ∫(z, q))

    reform_state = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model)
    DP.copy_and_reformulate(
        model, reform_state.decision_vars, Hull(), reform_state)
    w = reform_state.weights[z]

    # 10 Monte Carlo nodes at 1/10 each on top of the 3 original
    # supports, which the measure never touches
    @test length(w) == 13
    @test count(!iszero, w) == 10
    @test all(v -> iszero(v) || v ≈ 0.1, w)
    # total weight = measure of the domain [0, 1]^2
    @test sum(w) ≈ 1.0
end

# The measure collector reaches a measure inside a quadratic
# objective: the support_sum coefficients (one per support) become
# the weights instead of the trapezoid rule.
function test_quadrature_weights_quadratic_objective()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    @infinite_parameter(model, t in [0, 1], num_supports = 3)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))
    @constraint(model, x >= 5, Disjunct(Y[1]))
    @constraint(model, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)
    @objective(model, Min, support_sum(x, t)^2)

    reform_state = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model)
    DP.copy_and_reformulate(
        model, reform_state.decision_vars, Hull(), reform_state)
    @test reform_state.weights[x] == [1.0, 1.0, 1.0]
end

# Same through a nonlinear objective with a numeric literal; the
# model carries no optimizer so the transcription accepts the
# nonlinear objective.
function test_quadrature_weights_nonlinear_objective()
    model = InfiniteGDPModel()
    @infinite_parameter(model, t in [0, 1], num_supports = 3)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))
    @constraint(model, x >= 5, Disjunct(Y[1]))
    @constraint(model, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)
    @objective(model, Min, exp(support_sum(x, t)) + 2)

    reform_state = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model)
    DP.copy_and_reformulate(
        model, reform_state.decision_vars, Hull(), reform_state)
    @test reform_state.weights[x] == [1.0, 1.0, 1.0]
end

# Measure data that reports no coefficients of its own warns and
# falls through to the default weighting.
struct _UnreadableMeasureData <: InfiniteOpt.AbstractMeasureData end

function test_quadrature_weights_unreadable_measure_data()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    @infinite_parameter(model, t ∈ [0, 1], num_supports = 3)
    supps = [0.0, 0.5, 1.0]
    weights = nothing
    @test_logs (:warn,) begin
        weights = IDP._group_weights(_UnreadableMeasureData(), t, supps)
    end
    # same as the unmeasured path: UniTrapezoid on 3 uniform supports
    @test weights == IDP._group_weights(nothing, t, supps)
    @test weights == Dict(0.0 => 0.25, 0.5 => 0.5, 1.0 => 0.25)
end

# The cut coefficients carry the quadrature weights:
# ξ_k = 2 ω_k (sep_k - rBM_k) on each transcribed variable.
function test_add_cut_weighted_coefficients()
    model = InfiniteGDPModel(HiGHS.Optimizer)
    set_silent(model)
    @infinite_parameter(model, t ∈ [0, 1], num_supports = 3)
    @variable(model, 0 <= x <= 10, Infinite(t))
    @variable(model, Y[1:2], InfiniteLogical(t))
    @constraint(model, x >= 5, Disjunct(Y[1]))
    @constraint(model, x <= 3, Disjunct(Y[2]))
    @disjunction(model, Y)
    @objective(model, Min, ∫(x, t))

    # store the weights the way the CP loop does
    reform_state = DP._CuttingPlanes(CuttingPlanes(HiGHS.Optimizer), model)
    DP.copy_and_reformulate(
        model, reform_state.decision_vars, Hull(), reform_state)

    DP.reformulate_model(model, BigM(10.0))
    InfiniteOpt.build_transformation_backend!(model)
    transcribed = InfiniteOpt.transformation_model(model)
    rBM_sol = Dict(x => [1.0, 2.0, 3.0])
    sep_sol = Dict(x => [0.5, 1.5, 2.5])
    # the cut call consumes reform_state.decision_vars; restrict to x
    reform_state.decision_vars = [x]
    DP.add_cut(model, reform_state, rBM_sol, sep_sol)

    # UniTrapezoid on 3 uniform supports: [0.25, 0.5, 0.25]
    cut = JuMP.constraint_object(last(JuMP.all_constraints(
        transcribed, JuMP.AffExpr, MOI.GreaterThan{Float64})))
    xs = vec(InfiniteOpt.transformation_variable(x))
    expected = 2 .* [0.25, 0.5, 0.25] .* (-0.5)
    for k in eachindex(xs)
        @test JuMP.coefficient(cut.func, xs[k]) ≈ expected[k]
    end
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
        test_is_parameter()
        test_is_parameter_concrete_dispatches()
        test_requires_disaggregation()
        test_parameter_bound_info()
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
        test_disaggregate_expression_parameter()
    end

    @testset "Conic" begin
        test_conic_hull_infinite()
        test_conic_bigm_infinite()
        test_conic_all_cones_infinite()
        test_conic_constant_row_infinite()
    end

    @testset "Exact Quadratic Hull" begin
        test_split_quad_terms_infinite()
        test_epsilon_quad_hull_parameter()
        test_gehr_infinite()
        test_cehr_infinite()
        test_cehr_conic_infinite()
        test_cehr_epigraph_finite()
    end

    @testset "MBM" begin
        test_interpolate()
        test_raw_M_infinite_scalar()
        test_raw_M_infinite_param_function()
        test_mbm_finite_and_integer_var()
        test_mbm_infinite_simple()
        test_mbm_infinite_param_dependent()
        test_mbm_vs_bigm_infinite()
        test_mbm_with_derivatives()
    end

    @testset "Integration" begin
        test_infiniteopt_extension()
        test_methods()
        test_conic_methods_infinite()
        test_exact_quad_methods_infinite()
        test_cehr_conic_methods_infinite()
        test_exact_quad_ground_truth()
    end

    @testset "Cutting Planes" begin
        test_extract_solution_infinite()
        test_add_cut_infinite()
        test_quadrature_weights_trapezoid()
        test_quadrature_weights_gauss()
        test_quadrature_weights_multiparameter()
        test_quadrature_weights_default_fallbacks()
        test_quadrature_weights_dependent_groups()
        test_quadrature_weights_dependent_group_measure()
        test_quadrature_weights_quadratic_objective()
        test_quadrature_weights_nonlinear_objective()
        test_quadrature_weights_unreadable_measure_data()
        test_add_cut_weighted_coefficients()
        test_CuttingPlanes_infinite_simple()
        test_CuttingPlanes_infinite_two_disj()
        test_CuttingPlanes_with_cuts()
        test_CuttingPlanes_multiparameter()
    end

end
