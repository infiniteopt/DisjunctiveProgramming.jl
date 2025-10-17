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
    T = JuMP.value_type(M)
    info = JuMP.VariableInfo(
        true,      # has_lb = true
        lb,        # lower_bound = lb
        true,      # has_ub = true  
        ub,        # upper_bound = ub
        false,     # has_fix = false
        zero(T),   # fixed_value = 0
        false,     # has_start = false
        zero(T),   # start = 0
        false,     # binary = false
        false      # integer = false
    )
    properties = VariableProperties(info, "$(vref)_$(lvref)", nothing, nothing)
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

################################################################################
#                              VARIABLE AGGREGATION
################################################################################
function _aggregate_variable(
    model::M, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    vref::V, 
    method::_Hull
    ) where {M <: JuMP.AbstractModel, V <: JuMP.AbstractVariableRef}
    JuMP.is_binary(vref) && return #skip binary variables
    # con_expr = JuMP.@expression(model, -vref + sum(method.disjunction_variables[vref]))
    # push!(ref_cons, JuMP.build_constraint(error, con_expr, _MOI.EqualTo(0)))

    expr = Base.zero(JuMP.GenericAffExpr{JuMP.value_type(M), V})
    JuMP.add_to_expression!(expr, -1.0, vref)
    #TODO: One(T)
    for dv in method.disjunction_variables[vref]
        JuMP.add_to_expression!(expr, 1.0, dv)
    end
    
    push!(ref_cons, JuMP.build_constraint(error, expr, _MOI.EqualTo(0)))
    return 
end

################################################################################
#                              CONSTRAINT DISAGGREGATION
################################################################################
# variable
function _disaggregate_expression(
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
function _disaggregate_expression(
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
function _disaggregate_expression(
    model::JuMP.AbstractModel, 
    quad::JuMP.GenericQuadExpr, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    method::_Hull
    )
    #get affine part
    new_expr = _disaggregate_expression(model, quad.aff, bvref, method)
    #get quadratic part
    ϵ = method.value
    for (pair, coeff) in quad.terms
        da_ref = method.disjunct_variables[pair.a, bvref]
        db_ref = method.disjunct_variables[pair.b, bvref]
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
    return reformulate_disjunction(model, disj, Hull(method.value))
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel, 
    con::JuMP.ScalarConstraint{T, S}, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    method::_Hull
) where {T <: JuMP.AbstractJuMPScalar, S <: Union{_MOI.LessThan, _MOI.GreaterThan, _MOI.EqualTo}}
    new_func = _disaggregate_expression(model, con.func, bvref, method)
    set_value = _set_value(con.set)
    new_func -= set_value*bvref
    reform_con = JuMP.build_constraint(error, new_func, S(0))
    return [reform_con]
end
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel, 
    con::JuMP.VectorConstraint{T, S, R}, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr}, 
    method::_Hull
) where {T <: JuMP.AbstractJuMPScalar, S <: Union{_MOI.Nonpositives, _MOI.Nonnegatives, _MOI.Zeros}, R}
    new_func = JuMP.@expression(model, [i=1:con.set.dimension],
        _disaggregate_expression(model, con.func[i], bvref, method)
    )
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
    new_func = _disaggregate_expression(model, con.func, bvref, method)
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
