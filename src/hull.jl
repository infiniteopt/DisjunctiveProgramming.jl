################################################################################
#                              VARIABLE DISAGGREGATION
################################################################################
requires_disaggregation(vref::JuMP.GenericVariableRef) = true
function requires_disaggregation(::V) where {V}
    error("`Hull` method does not support expressions with variable " *
          "references of type `$V`.")
end

function _disaggregate_variables(
    model::JuMP.AbstractModel, 
    lvref::LogicalVariableRef, 
    vrefs::Set, 
    method::_Hull
    )
    #create disaggregated variables for that disjunct
    for vref in vrefs
        if !requires_disaggregation(vref) || JuMP.is_binary(vref) 
            continue # skip variables that don't require dissagregation
        end
        _disaggregate_variable(model, lvref, vref, method) #create disaggregated var for that disjunct
    end
end

function _disaggregate_variable(
    model::M, 
    lvref::LogicalVariableRef, 
    vref::JuMP.AbstractVariableRef, 
    method::_Hull
    ) where {M <: JuMP.AbstractModel}
    #create disaggregated vref
    lb, ub = variable_bound_info(vref)
    info = get_variable_info(vref; has_lb = true, has_ub = true, 
                             lower_bound = lb, upper_bound = ub)
    old_props = VariableProperties(vref)
    properties = VariableProperties(info, "$(vref)_$(lvref)", 
                                    old_props.set, old_props.variable_type)
    dvref = create_variable(model, properties)
    push!(_reformulation_variables(model), dvref)
    #get binary indicator variable
    bvref = binary_variable(lvref)
    #temp storage
    push!(method.disjunction_variables[vref], dvref)
    method.disjunct_variables[vref, bvref] = dvref
    #create bounding constraints
    dvname = JuMP.name(dvref)
    lbname = isempty(dvname) ? "" : "$(dvname)_lower_bound"
    ubname = isempty(dvname) ? "" : "$(dvname)_upper_bound"
    new_con_lb_ref = JuMP.@constraint(model, lb*bvref - dvref <= 0, base_name = lbname)
    new_con_ub_ref = JuMP.@constraint(model, dvref - ub*bvref <= 0, base_name = ubname)
    push!(_reformulation_constraints(model), new_con_lb_ref, new_con_ub_ref)
    return dvref
end

#TODO: Throw error for fix, bin, integer
################################################################################
#                              VARIABLE AGGREGATION
################################################################################
function _aggregate_variable(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    vref::JuMP.AbstractVariableRef, 
    method::_Hull
    )

    JuMP.is_binary(vref) && return #skip binary variables
    if isempty(method.disjunction_variables[vref])
        return  # Variable wasn't disaggregated, skip aggregation
    end
    con_expr = JuMP.@expression(model, -vref + sum(method.disjunction_variables[vref]))
    push!(ref_cons, JuMP.build_constraint(error, con_expr, _MOI.EqualTo(0)))
    return 
end

################################################################################
#                              CONSTRAINT DISAGGREGATION
################################################################################
# variable
"""
    disaggregate_expression(
        model::JuMP.AbstractModel,
        expr,
        bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
        method::_Hull
    )

Disaggregate an expression for the Hull reformulation. This function is dispatched 
based on the expression type:

- `vref::JuMP.AbstractVariableRef`: Returns the disaggregated variable if it exists, 
  otherwise returns the original variable (for binary variables or nested disaggregated variables).
- `aff::JuMP.GenericAffExpr`: Disaggregates each term in the affine expression.
- `quad::JuMP.GenericQuadExpr`: Disaggregates both the affine and quadratic parts of the expression.

The disaggregated expression is multiplied by the binary indicator variable `bvref` 
to enforce the disjunctive constraint.
"""
function disaggregate_expression(
    model::JuMP.AbstractModel, 
    vref::JuMP.AbstractVariableRef, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    method::_Hull
    )
    if JuMP.is_binary(vref) || !haskey(method.disjunct_variables, (vref, bvref)) #keep any binary variables or nested disaggregated variables unchanged 
        return vref #NOTE: not needed because nested constraint of the form `vref in MOI.AbstractScalarSet` gets reformulated to an affine expression.
    else #replace with disaggregated form
        return method.disjunct_variables[vref, bvref]
    end
end
# affine expression
function disaggregate_expression(
    model::JuMP.AbstractModel, 
    aff::JuMP.GenericAffExpr, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    method::_Hull
    )
    new_expr = @expression(model, aff.constant*bvref) #multiply constant by binary indicator variable
    for (vref, coeff) in aff.terms
        if JuMP.is_binary(vref) || !haskey(method.disjunct_variables, (vref, bvref)) #keep any binary variables or nested disaggregated variables unchanged 
            JuMP.add_to_expression!(new_expr, coeff*vref)
        else #replace other vars with disaggregated form
            dvref = method.disjunct_variables[vref, bvref]
            JuMP.add_to_expression!(new_expr, coeff*dvref)
        end
    end
    return new_expr
end

# quadratic expression
# TODO review what happens when there are bilinear terms with binary variables involved since these are not being disaggregated 
#   (e.g., complementarity constraints; though likely irrelevant)...
function disaggregate_expression(
    model::JuMP.AbstractModel, 
    quad::JuMP.GenericQuadExpr, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    method::_Hull
    )
    quad_part, affine_part = _split_quad_terms(quad)
    new_expr = _disaggregate_affine_terms(model, affine_part, bvref, method)
    ϵ = method.value
    for (pair, coeff) in quad_part.terms
        da_ref = disaggregate_expression(model, pair.a, bvref, method)
        db_ref = disaggregate_expression(model, pair.b, bvref, method)
        new_expr += coeff * da_ref * db_ref / ((1-ϵ)*bvref+ϵ)
    end
    return new_expr
end
# constant in NonlinearExpr
function _disaggregate_nl_expression(
    ::JuMP.AbstractModel, 
    c::Number, 
    ::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    ::_Hull
    )
    return c
end
# variable in NonlinearExpr
function _disaggregate_nl_expression(
    ::JuMP.AbstractModel, 
    vref::JuMP.AbstractVariableRef, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    method::_Hull
    )
    ϵ = method.value
    if JuMP.is_binary(vref) || !haskey(method.disjunct_variables, (vref, bvref)) #keep any binary variables or nested disaggregated variables unchanged 
        dvref = vref
    else #replace with disaggregated form
        dvref = method.disjunct_variables[vref, bvref]
    end
    return dvref / ((1-ϵ)*bvref+ϵ)
end
# affine expression in NonlinearExpr
function _disaggregate_nl_expression(
    ::JuMP.AbstractModel, 
    aff::JuMP.GenericAffExpr, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    method::_Hull
    )
    new_expr = aff.constant
    ϵ = method.value
    for (vref, coeff) in aff.terms
        if JuMP.is_binary(vref) || !haskey(method.disjunct_variables, (vref, bvref)) #keep any binary variables or nested disaggregated variables unchanged 
            dvref = vref
        else #replace other vars with disaggregated form
            dvref = method.disjunct_variables[vref, bvref]
        end
        new_expr += coeff * dvref / ((1-ϵ)*bvref+ϵ)
    end
    return new_expr
end
# quadratic expression in NonlinearExpr
# TODO review what happens when there are bilinear terms with binary variables involved since these are not being disaggregated 
#   (e.g., complementarity constraints; though likely irrelevant)...
function _disaggregate_nl_expression(
    model::JuMP.AbstractModel, 
    quad::JuMP.GenericQuadExpr, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    method::_Hull)
    #get affine part
    new_expr = _disaggregate_nl_expression(model, quad.aff, bvref, method)
    #get quadratic part
    ϵ = method.value
    for (pair, coeff) in quad.terms
        da_ref = method.disjunct_variables[pair.a, bvref]
        db_ref = method.disjunct_variables[pair.b, bvref]
        new_expr += coeff * da_ref * db_ref / ((1-ϵ)*bvref+ϵ)^2
    end
    return new_expr
end
# nonlinear expression in NonlinearExpr
function _disaggregate_nl_expression(
    model::JuMP.AbstractModel, 
    nlp::NLP, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    method::_Hull
    ) where {NLP <: JuMP.GenericNonlinearExpr}
    new_args = Vector{Any}(undef, length(nlp.args))
    for (i,arg) in enumerate(nlp.args)
        new_args[i] = _disaggregate_nl_expression(model, arg, bvref, method)
    end
    new_expr = NLP(nlp.head, new_args)
    return new_expr
end

################################################################################
#                              HULL REFORMULATION
################################################################################
requires_exactly1(::Hull) = true

requires_variable_bound_info(::Hull) = true

function set_variable_bound_info(vref::JuMP.AbstractVariableRef, ::Hull)
    if !has_lower_bound(vref) || !has_upper_bound(vref)
        error("Variable $vref must have both lower and upper bounds defined when using the Hull reformulation.")
    else
        lb = min(0, lower_bound(vref))
        ub = max(0, upper_bound(vref))
    end
    return lb, ub
end

function reformulate_disjunction(model::JuMP.AbstractModel, disj::Disjunction, method::Hull)
    ref_cons = Vector{AbstractConstraint}() #store reformulated constraints
    disj_vrefs = _get_disjunction_variables(model, disj)
    hull = _Hull(method, disj_vrefs)
    for d in disj.indicators #reformulate each disjunct
        _disaggregate_variables(model, d, disj_vrefs, hull) #disaggregate variables for that disjunct
        _reformulate_disjunct(model, ref_cons, d, hull)
    end
    for vref in disj_vrefs #create sum constraint for disaggregated variables
        _aggregate_variable(model, ref_cons, vref, hull)
    end
    return ref_cons
end
function reformulate_disjunction(model::JuMP.AbstractModel, disj::Disjunction, method::_Hull)
    hull = Hull(method.value; quadratic = method.quadratic)
    return reformulate_disjunction(model, disj, hull)
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel, 
    con::JuMP.ScalarConstraint{T, S}, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    method::_Hull
) where {T <: JuMP.AbstractJuMPScalar, S <: Union{_MOI.LessThan, _MOI.GreaterThan, _MOI.EqualTo}}
    new_func = disaggregate_expression(model, con.func, bvref, method)
    set_value = _set_value(con.set)
    new_func -= set_value*bvref
    reform_con = JuMP.build_constraint(error, new_func, S(0))
    return [reform_con]
end

# Promote disaggregated vector rows to one concrete expression type
# (rows mix affine and quadratic when parameters scale the indicator)
function _combine_expressions(exprs::Vector)
    T = mapreduce(typeof, promote_type, exprs)
    return convert.(T, exprs)
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
) where {T <: JuMP.AbstractJuMPScalar, S <: Union{_MOI.Nonpositives, _MOI.Nonnegatives, _MOI.Zeros}, R}
    new_func = _combine_expressions([
        disaggregate_expression(model, func, bvref, method)
        for func in con.func
    ])
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
) where {
    T <: Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    S <: _ConicSets, R
}
    new_func = _combine_expressions([
        disaggregate_expression(model, func, bvref, method)
        for func in con.func
    ])
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel, 
    con::JuMP.ScalarConstraint{T, S}, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
) where {T <: JuMP.GenericNonlinearExpr, S <: Union{_MOI.LessThan, _MOI.GreaterThan, _MOI.EqualTo}}
    con_func = _disaggregate_nl_expression(model, con.func, bvref, method)
    con_func0 = JuMP.value(v -> 0.0, con.func)
    if isinf(con_func0)
        error("Operator `$(con.func.head)` is not defined at 0, causing the perspective function on the Hull reformulation to fail.")
    end
    ϵ = method.value
    set_value = _set_value(con.set)
    new_func = JuMP.@expression(model, ((1-ϵ)*bvref+ϵ)*con_func - ϵ*(1-bvref)*con_func0 - set_value*bvref)
    reform_con = JuMP.build_constraint(error, new_func, S(0))
    return [reform_con]
end
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel, 
    con::JuMP.VectorConstraint{T, S, R}, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
) where {T <: JuMP.GenericNonlinearExpr, S <: Union{_MOI.Nonpositives, _MOI.Nonnegatives, _MOI.Zeros}, R}
    con_func = JuMP.@expression(model, [i=1:con.set.dimension],
        _disaggregate_nl_expression(model, con.func[i], bvref, method)
    )
    con_func0 = JuMP.value.(v -> 0.0, con.func)
    if any(isinf.(con_func0))
        error("At least of of the operators `$([func.head for func in con.func])` is not defined at 0, causing the perspective function on the Hull reformulation to fail.")
    end
    ϵ = method.value
    new_func = JuMP.@expression(model, [i=1:con.set.dimension], 
        ((1-ϵ)*bvref+ϵ)*con_func[i] - ϵ*(1-bvref)*con_func0[i]
    )
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel, 
    con::JuMP.ScalarConstraint{T, S}, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
) where {T <: JuMP.AbstractJuMPScalar, S <: _MOI.Interval}
    new_func = disaggregate_expression(model, con.func, bvref, method)
    new_func_gt = JuMP.@expression(model, new_func - con.set.lower*bvref)
    new_func_lt = JuMP.@expression(model, new_func - con.set.upper*bvref)
    reform_con_gt = JuMP.build_constraint(error, new_func_gt, _MOI.GreaterThan(0))
    reform_con_lt = JuMP.build_constraint(error, new_func_lt, _MOI.LessThan(0))
    return [reform_con_gt, reform_con_lt]
end
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
) where {T <: JuMP.GenericNonlinearExpr, S <: _MOI.Interval}
    con_func = _disaggregate_nl_expression(model, con.func, bvref, method)
    con_func0 = JuMP.value(v -> 0.0, con.func)
    if isinf(con_func0)
        error("Operator `$(con.func.head)` is not defined at 0, causing the perspective function on the Hull reformulation to fail.")
    end
    ϵ = method.value
    new_func = JuMP.@expression(model, ((1-ϵ)*bvref+ϵ) * con_func - ϵ*(1-bvref)*con_func0)
    new_func_gt = JuMP.@expression(model, new_func - con.set.lower*bvref)
    new_func_lt = JuMP.@expression(model, new_func - con.set.upper*bvref)
    reform_con_gt = JuMP.build_constraint(error, new_func_gt, _MOI.GreaterThan(0))
    reform_con_lt = JuMP.build_constraint(error, new_func_lt, _MOI.LessThan(0))
    return [reform_con_gt, reform_con_lt]
end

################################################################################
#                       EXACT QUADRATIC HULL (GEHR / CEHR)
################################################################################
# Exact hull reformulations for quadratic disjunct constraints
# (Gusev & Bernal Neira 2025, arXiv:2508.16093), replacing the
# ε-approximated perspective. Both are exact for the full relaxation
# y ∈ [0, 1] given finite variable bounds (the disaggregated variable
# bounds force ν = 0 when y = 0):
# - GEHR (Eq. 13): multiply cl h̃(ν, y) ≤ 0 through by y to get
#   ν'Qν + (a'ν)y + d*y² ≤ 0. Valid for any Q (nonconvex included)
#   and for equalities, but the function is nonconvex in (ν, y).
# - CEHR (Eq. 22): for convex constraints (Q ⪰ 0), epigraph variable
#   t ≥ 0 with ν'Qν - t*y ≤ 0 and t + a'ν + d*y ≤ 0. The cone
#   constraint is left unfactorized so conic-aware solvers recognize
#   the rotated SOC in presolve; at y = 0 the link forces t = 0.

# Assemble the symmetric coefficient matrix of the quadratic terms and
# the variables indexing its rows, in order of first appearance
function _quad_coefficient_matrix(
    quad::JuMP.GenericQuadExpr{C, V}
    ) where {C, V}
    index = Dict{V, Int}()
    vars = V[]
    for (pair, _) in quad.terms, v in (pair.a, pair.b)
        haskey(index, v) || (push!(vars, v); index[v] = length(vars))
    end
    quad_matrix = zeros(float(C), length(vars), length(vars))
    for (pair, coeff) in quad.terms
        i, j = index[pair.a], index[pair.b]
        if i == j
            quad_matrix[i, i] += coeff
        else
            quad_matrix[i, j] += coeff / 2
            quad_matrix[j, i] += coeff / 2
        end
    end
    return quad_matrix, vars
end

# Check whether the quadratic part is convex (Q ⪰ 0 up to a tolerance)
function _is_convex_quad(quad::JuMP.GenericQuadExpr)
    quad_matrix, _ = _quad_coefficient_matrix(quad)
    tol = 1e-9 * max(one(eltype(quad_matrix)), maximum(abs, quad_matrix))
    return LinearAlgebra.eigmin(LinearAlgebra.Symmetric(quad_matrix)) >= -tol
end

# Split the quadratic terms into `quad_part` (both factors get
# disaggregated) and `affine_part` (coefficient-only factors such as
# infinite parameters, plus the affine part), which is affine in the
# disaggregated variables
function _split_quad_terms(quad::JuMP.GenericQuadExpr)
    quad_part = zero(typeof(quad))
    affine_part = typeof(quad)(copy(quad.aff))
    for (pair, coeff) in quad.terms
        if requires_disaggregation(pair.a) &&
            requires_disaggregation(pair.b)
            JuMP.add_to_expression!(quad_part, coeff, pair.a, pair.b)
        else
            JuMP.add_to_expression!(affine_part, coeff, pair.a, pair.b)
        end
    end
    return quad_part, affine_part
end

# Disaggregate the remainder terms: coefficient-only factors scale
# with the indicator like constants do
function _disaggregate_affine_terms(
    model::JuMP.AbstractModel,
    affine_part::JuMP.GenericQuadExpr,
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
    )
    new_expr = disaggregate_expression(model, affine_part.aff, bvref, method)
    for (pair, coeff) in affine_part.terms
        if requires_disaggregation(pair.a)
            dref = disaggregate_expression(model, pair.a, bvref, method)
            new_expr = JuMP.@expression(model,
                new_expr + coeff*dref*pair.b)
        elseif requires_disaggregation(pair.b)
            dref = disaggregate_expression(model, pair.b, bvref, method)
            new_expr = JuMP.@expression(model,
                new_expr + coeff*pair.a*dref)
        else
            new_expr = JuMP.@expression(model,
                new_expr + coeff*pair.a*pair.b*bvref)
        end
    end
    return new_expr
end

# Disaggregate the quadratic terms without the ε-perspective division
function _disaggregate_quad_terms(
    model::JuMP.AbstractModel,
    quad::JuMP.GenericQuadExpr,
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
    )
    new_expr = zero(typeof(quad))
    for (pair, coeff) in quad.terms
        da_ref = disaggregate_expression(model, pair.a, bvref, method)
        db_ref = disaggregate_expression(model, pair.b, bvref, method)
        JuMP.add_to_expression!(new_expr, coeff, da_ref, db_ref)
    end
    return new_expr
end

# GEHR expression (Eq. 13) for a constraint normalized to h(x) vs 0:
# ν'Qν + (a'ν)*y + d*y²
function _gehr_expression(
    model::JuMP.AbstractModel,
    h::JuMP.GenericQuadExpr,
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
    )
    quad_part, affine_part = _split_quad_terms(h)
    quad_part = _disaggregate_quad_terms(model, quad_part, bvref, method)
    affine_part = _disaggregate_affine_terms(model, affine_part, bvref, method)
    return JuMP.@expression(model, quad_part + affine_part*bvref)
end

# Add the CEHR epigraph variable t >= 0 for one quadratic constraint;
# its type is inferred from the constraint function so extensions can
# match it to the constraint (e.g. infinite over its parameters)
function _add_cehr_epigraph_variable(
    model::JuMP.AbstractModel,
    h::JuMP.GenericQuadExpr,
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}
    )
    base = "t_cehr_$(bvref)"
    n = count(
        v -> startswith(JuMP.name(v), base),
        _reformulation_variables(model)
    )
    epigraph_vref = create_variable(model, VariableProperties(h))
    JuMP.set_lower_bound(epigraph_vref, 0)
    JuMP.set_name(epigraph_vref, n == 0 ? base : "$(base)_$(n + 1)")
    push!(_reformulation_variables(model), epigraph_vref)
    return epigraph_vref
end

# CEHR for solvers that accept cones: the quadratic is handed over as
# an explicit rotated second-order cone
function _cehr_conic_constraints(
    model::JuMP.AbstractModel,
    h::JuMP.GenericQuadExpr,
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
    )
    quad_part, affine_part = _split_quad_terms(h)
    epigraph_vref = _add_cehr_epigraph_variable(model, h, bvref)
    quad_matrix, vars = _quad_coefficient_matrix(quad_part)
    factors = LinearAlgebra.eigen(LinearAlgebra.Symmetric(quad_matrix))
    tol = 1e-9 * max(one(eltype(quad_matrix)), maximum(abs, quad_matrix))
    dvars = [disaggregate_expression(model, v, bvref, method)
             for v in vars]
    rows = [0.5 * epigraph_vref, zero(0.5 * epigraph_vref) + bvref]
    for k in findall(>(tol), factors.values) # drop zero eigenvalues
        push!(rows, sqrt(factors.values[k]) * sum(
            factors.vectors[j, k] * dvars[j] for j in eachindex(dvars)))
    end
    affine_part = _disaggregate_affine_terms(model, affine_part, bvref, method)
    epigraph_link = JuMP.@expression(model, epigraph_vref + affine_part)
    return [
        JuMP.build_constraint(error, rows,
            _MOI.RotatedSecondOrderCone(length(rows))),
        JuMP.build_constraint(error, epigraph_link, _MOI.LessThan(0))
    ]
end

# Reformulate a quadratic constraint normalized to h(x) ≤ 0 exactly:
# CEHR when the quadratic part is convex (unless `:gehr` is forced),
# GEHR otherwise. CEHR stays algebraic for solvers that do not accept
# cones; `:cehr_conic` writes the cone out for solvers that do.
function _exact_quad_hull(
    model::JuMP.AbstractModel,
    h::JuMP.GenericQuadExpr,
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
    )
    quad_part, affine_part = _split_quad_terms(h)
    if isempty(quad_part.terms) # affine in the disaggregated variables
        affine_part = _disaggregate_affine_terms(
            model, affine_part, bvref, method)
        return [JuMP.build_constraint(error, affine_part, _MOI.LessThan(0))]
    elseif _is_convex_quad(quad_part) && method.quadratic == :cehr_conic
        return _cehr_conic_constraints(model, h, bvref, method)
    elseif _is_convex_quad(quad_part) && method.quadratic != :gehr
        epigraph_vref = _add_cehr_epigraph_variable(model, h, bvref)
        quad_part = _disaggregate_quad_terms(model, quad_part, bvref, method)
        affine_part = _disaggregate_affine_terms(
            model, affine_part, bvref, method)
        cone_func = JuMP.@expression(model, quad_part - epigraph_vref*bvref)
        epigraph_link = JuMP.@expression(model, epigraph_vref + affine_part)
        return [
            JuMP.build_constraint(error, cone_func, _MOI.LessThan(0)),
            JuMP.build_constraint(error, epigraph_link, _MOI.LessThan(0))
        ]
    elseif method.quadratic in (:cehr, :cehr_conic)
        error("`Hull(quadratic = :$(method.quadratic))` requires convex " *
              "quadratic disjunct constraints. Use `quadratic = :exact` " *
              "or `quadratic = :gehr` for nonconvex quadratic constraints.")
    else
        gehr_func = _gehr_expression(model, h, bvref, method)
        return [JuMP.build_constraint(error, gehr_func, _MOI.LessThan(0))]
    end
end

# Reformulate a quadratic equality normalized to h(x) = 0 exactly
# (GEHR; CEHR does not apply since quadratic equalities are nonconvex)
function _exact_quad_hull_eq(
    model::JuMP.AbstractModel,
    h::JuMP.GenericQuadExpr,
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
    )
    quad_part, affine_part = _split_quad_terms(h)
    if isempty(quad_part.terms) # affine in the disaggregated variables
        affine_part = _disaggregate_affine_terms(
            model, affine_part, bvref, method)
        return [JuMP.build_constraint(error, affine_part, _MOI.EqualTo(0))]
    elseif method.quadratic in (:cehr, :cehr_conic)
        error("`Hull(quadratic = :$(method.quadratic))` does not support " *
              "quadratic equality constraints. Use `quadratic = :exact` " *
              "or `quadratic = :gehr` instead.")
    end
    gehr_func = _gehr_expression(model, h, bvref, method)
    return [JuMP.build_constraint(error, gehr_func, _MOI.EqualTo(0))]
end

# scalar quadratic constraint
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
) where {
    T <: JuMP.GenericQuadExpr,
    S <: Union{_MOI.LessThan, _MOI.GreaterThan, _MOI.EqualTo}
}
    set_value = _set_value(con.set)
    if method.quadratic == :epsilon # ε-approximated perspective
        new_func = disaggregate_expression(model, con.func, bvref, method)
        new_func -= set_value*bvref
        return [JuMP.build_constraint(error, new_func, S(0))]
    elseif S <: _MOI.EqualTo
        return _exact_quad_hull_eq(model, con.func - set_value, bvref, method)
    else # normalize to h(x) ≤ 0 (flip GreaterThan constraints)
        h = S <: _MOI.LessThan ? con.func - set_value : set_value - con.func
        return _exact_quad_hull(model, h, bvref, method)
    end
end
# scalar quadratic constraint in an interval
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
) where {T <: JuMP.GenericQuadExpr, S <: _MOI.Interval}
    if method.quadratic == :epsilon # ε-approximated perspective
        new_func = disaggregate_expression(model, con.func, bvref, method)
        new_func_gt = JuMP.@expression(model, new_func - con.set.lower*bvref)
        new_func_lt = JuMP.@expression(model, new_func - con.set.upper*bvref)
        return [
            JuMP.build_constraint(error, new_func_gt, _MOI.GreaterThan(0)),
            JuMP.build_constraint(error, new_func_lt, _MOI.LessThan(0))
        ]
    end
    return vcat(
        _exact_quad_hull(model, con.func - con.set.upper, bvref, method),
        _exact_quad_hull(model, con.set.lower - con.func, bvref, method)
    )
end
# vector quadratic constraint
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::_Hull
) where {
    T <: JuMP.GenericQuadExpr,
    S <: Union{_MOI.Nonpositives, _MOI.Nonnegatives, _MOI.Zeros}, R
}
    if method.quadratic == :epsilon # ε-approximated perspective
        new_func = _combine_expressions([
            disaggregate_expression(model, func, bvref, method)
            for func in con.func
        ])
        return [JuMP.build_constraint(error, new_func, con.set)]
    end
    reform_cons = Vector{AbstractConstraint}()
    for func in con.func # normalize each entry to h(x) ≤ 0 or h(x) = 0
        h = S <: _MOI.Nonnegatives ? -func : func
        if S <: _MOI.Zeros
            append!(reform_cons, _exact_quad_hull_eq(model, h, bvref, method))
        else
            append!(reform_cons, _exact_quad_hull(model, h, bvref, method))
        end
    end
    return reform_cons
end
