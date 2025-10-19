################################################################################
#                              BUILD PARTITIONED EXPRESSION
################################################################################

function _build_partitioned_expression(
    expr::T,
    partition_variables::Vector{<:JuMP.AbstractVariableRef}
) where {T <: JuMP.GenericAffExpr}
    constant = JuMP.constant(expr)
    new_affexpr = zero(T)
    for var in partition_variables
        JuMP.add_to_expression!(new_affexpr, JuMP.coefficient(expr, var), var) 
    end
    return new_affexpr, constant
end

function _build_partitioned_expression(
    expr::T,
    partition_variables::Vector{<:JuMP.AbstractVariableRef}
) where {T <: JuMP.GenericQuadExpr}
    new_quadexpr = zero(T)
    constant = JuMP.constant(expr)
    for var in partition_variables
        for (pair, coeff) in expr.terms
            if pair.a == var && pair.b == var
                JuMP.add_to_expression!(new_quadexpr, coeff, var, var)
            elseif pair.a == var || pair.b == var
                error("Quadratic expression contains 
                bilinear term ($(pair.a), $(pair.b))")
            end
            
        end
    end
    new_aff, _ = _build_partitioned_expression(expr.aff, partition_variables)
    JuMP.add_to_expression!(new_quadexpr, new_aff)
    return new_quadexpr, constant
end

function _build_partitioned_expression(
    expr::T,
    partition_variables::Vector{<:JuMP.AbstractVariableRef}
) where {T <: JuMP.AbstractVariableRef}

    if expr in partition_variables
        return expr, zero(T)
    else
        return zero(T), zero(T)
    end
end

function _build_partitioned_expression(
    expr::T,
    partition_variables::Vector{<:JuMP.AbstractVariableRef}
) where {T <: Number}
    return expr, zero(T)
end

function _build_partitioned_expression(
    expr::T,
    partition_variables::Vector{<:JuMP.AbstractVariableRef}
) where {T <: JuMP.GenericNonlinearExpr}
    error("P-Split does not currently support nonlinear expressions $(expr)")
end


################################################################################
#                              BOUND AUXILIARY
################################################################################
function _bound_auxiliary(
    model::M,
    v::JuMP.AbstractVariableRef,
    func::JuMP.GenericAffExpr{T,V},
    method::PSplit
) where {M <: JuMP.AbstractModel, T, V}

    lower_bound = has_lower_bound(v) ? lower_bound(v) : zero(T)
    upper_bound = has_upper_bound(v) ? upper_bound(v) : zero(T)

    for (var, coeff) in func.terms
        if var != v
            JuMP.is_binary(var) && continue
            var_lb, var_ub = variable_bound_info(var)
            if coeff > 0.0
                lower_bound += coeff * var_lb
                upper_bound += coeff * var_ub
            else
                lower_bound += coeff * var_ub
                upper_bound += coeff * var_lb
            end
        end
    end
    JuMP.set_lower_bound(v, lower_bound)
    JuMP.set_upper_bound(v, upper_bound)
    _variable_bounds(model)[v] = set_variable_bound_info(v, method)
end    

function _bound_auxiliary(
    model::M,
    v::JuMP.AbstractVariableRef,
    func::Number,
    method::PSplit
) where {M <: JuMP.AbstractModel}
    JuMP.set_lower_bound(v, func)
    JuMP.set_upper_bound(v, func)
    _variable_bounds(model)[v] = set_variable_bound_info(v, method)
    return
end

function _bound_auxiliary(
    model::M,
    v::JuMP.AbstractVariableRef,
    func::JuMP.GenericQuadExpr{T,V},
    method::PSplit
) where {M <: JuMP.AbstractModel, T, V}
    
    # Handle linear terms
    _bound_auxiliary(model, v, func.aff, method)
    lower_bound = JuMP.lower_bound(v)
    upper_bound = JuMP.upper_bound(v)
    
    # Handle quadratic terms
    for (vars, coeff) in func.terms
        var = vars.a 
        if var != v
            JuMP.is_binary(var) && continue
            lb, ub = variable_bound_info(var)
            
            # For x^2 terms
            sq_min = min(lb^2, ub^2, zero(T))
            sq_max = max(lb^2, ub^2, zero(T))
            
            if coeff > 0.0
                lower_bound += coeff * sq_min
                upper_bound += coeff * sq_max
            else
                lower_bound += coeff * sq_max
                upper_bound += coeff * sq_min
            end
        end
    end
    
    # Add constant term
    const_term = func.aff.constant
    # lower_bound += const_term
    # upper_bound += const_term
    
    JuMP.set_lower_bound(v, lower_bound)
    JuMP.set_upper_bound(v, upper_bound)
    _variable_bounds(model)[v] = set_variable_bound_info(v, method)
end

function _bound_auxiliary(
    model::M,
    v::JuMP.AbstractVariableRef,
    func::JuMP.AbstractVariableRef,
    method::PSplit
) where {M <: JuMP.AbstractModel}
    T = JuMP.value_type(M)
    lower_bound = zero(T)
    upper_bound = zero(T)
    if func != v
        lower_bound = variable_bound_info(func)[1]
        upper_bound = variable_bound_info(func)[2]
        JuMP.set_lower_bound(v, lower_bound)
        JuMP.set_upper_bound(v, upper_bound)
    else
        JuMP.set_lower_bound(v,lower_bound)
        JuMP.set_upper_bound(v,upper_bound)
    end
    _variable_bounds(model)[v] = set_variable_bound_info(v, method)
end

requires_variable_bound_info(method::Union{PSplit, _PSplit}) = true

function set_variable_bound_info(
    vref::JuMP.AbstractVariableRef, 
    ::Union{PSplit, _PSplit}
    )
    if !has_lower_bound(vref) || !has_upper_bound(vref)
        error("Variable $vref must have both lower and upper bounds defined when
         using the PSplit reformulation."
         )
    else
        lb = min(0, lower_bound(vref))
        ub = max(0, upper_bound(vref))
    end
    return lb, ub
end

################################################################################
#                              REFORMULATE DISJUNCT
################################################################################

function reformulate_disjunction(
    model::JuMP.AbstractModel, 
    disj::Disjunction, 
    method::PSplit{V}
) where {V <: JuMP.AbstractVariableRef}
    ref_cons = Vector{JuMP.AbstractConstraint}() #store reformulated constraints
    disj_vrefs = _get_disjunction_variables(model, disj)
    sum_constraints = Dict{LogicalVariableRef, Vector{<:JuMP.AbstractConstraint}}()
    aux_vars = Set{V}()
    for d in disj.indicators
        partitioned_constraints, sum_constraints[d], vars = _partition_disjunct(model, d, method)
        append!(ref_cons, partitioned_constraints)
        union!(aux_vars, vars)
    end
    psplit = _PSplit(method, model)
    psplit.hull = _Hull(Hull(), union(disj_vrefs, aux_vars))
    psplit.sum_constraints = sum_constraints
    for d in disj.indicators
        bvref = binary_variable(d)
        for vref in disj_vrefs
            push!(psplit.hull.disjunction_variables[vref], vref)
            psplit.hull.disjunct_variables[vref, bvref] = vref
        end
        _disaggregate_variables(model, d, aux_vars, psplit.hull)
        _reformulate_disjunct(model, ref_cons, d, psplit)
    end
    for vref in aux_vars
        _aggregate_variable(model, ref_cons, vref, psplit.hull)
    end
    return ref_cons
end

function reformulate_disjunction(
    model::JuMP.AbstractModel, 
    disj::Disjunction, 
    method::_PSplit
)
    return reformulate_disjunction(model, disj, PSplit(method.partition))
end

function _reformulate_disjunct(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef, 
    method::_PSplit
    )
    #reformulate each constraint and add to the model
    bvref = binary_variable(lvref)
    haskey(method.sum_constraints, lvref) || return
    constraints = method.sum_constraints[lvref]
    for con in constraints
        append!(ref_cons, reformulate_disjunct_constraint(model, con, bvref, method.hull))
    end
    return
end

function _partition_disjunct(
    model::M, 
    lvref::LogicalVariableRef, 
    method::PSplit
) where {M <: JuMP.AbstractModel}
    !haskey(_indicator_to_constraints(model), lvref) && return #skip if disjunct is empty
    
    partitioned_constraints = Vector{AbstractConstraint}()
    sum_constraints = Vector{AbstractConstraint}()
    aux_vars = Set{JuMP.AbstractVariableRef}()
    for cref in _indicator_to_constraints(model)[lvref] 
        con = JuMP.constraint_object(cref)
        if !(con isa Disjunction)
            part_con, sum_con, new_aux_vars = _build_partitioned_constraint(model, con, method)
            append!(partitioned_constraints, part_con)
            append!(sum_constraints, sum_con)
            union!(aux_vars, new_aux_vars)   
        end
    end
    return partitioned_constraints, sum_constraints, aux_vars
end

#################################################################################
#                              BUILD PARTITIONED CONSTRAINT
#################################################################################
function _build_partitioned_constraint(
    model::M,
    con::JuMP.ScalarConstraint{T, S},
    method::PSplit
) where {M <: JuMP.AbstractModel, T, S <: _MOI.LessThan}
    val_type = JuMP.value_type(M)
    p = length(method.partition)
    v = [@variable(model, base_name = "v_$(hash(con))_$(i)") for i in 1:p]
    _, constant = _build_partitioned_expression(con.func, method.partition[p])
    part_con = Vector{JuMP.AbstractConstraint}(undef, p)
    for i in 1:p
        func, _ = _build_partitioned_expression(con.func, method.partition[i])
        part_con[i] = JuMP.build_constraint(error, func - v[i], 
        MOI.LessThan(zero(val_type))
        )
        _bound_auxiliary(model, v[i], func, method)
    end
    sum_con = JuMP.build_constraint(error, sum(v[i] for i in 1:p) 
    ,MOI.LessThan(con.set.upper - constant)
    )

    return part_con, [sum_con], v
end

function _build_partitioned_constraint(
    model::M,
    con::JuMP.ScalarConstraint{T, S},
    method::PSplit
) where {M <: JuMP.AbstractModel, T, S <: _MOI.GreaterThan}
    val_type = JuMP.value_type(M)
    p = length(method.partition)
    part_con = Vector{JuMP.AbstractConstraint}(undef, p)
    v = [@variable(model, base_name = "v_$(hash(con))_$(i)") for i in 1:p]
    _, constant = _build_partitioned_expression(con.func, method.partition[p])
    for i in 1:p
        func, _ = _build_partitioned_expression(con.func, method.partition[i])
        part_con[i] = JuMP.build_constraint(error, -func - v[i], 
        MOI.LessThan(zero(val_type))
        )
        _bound_auxiliary(model, v[i], -func, method)
    end
    sum_con = JuMP.build_constraint(error, sum(v[i] for i in 1:p) 
    , MOI.LessThan(-con.set.lower + constant)
    )
    return part_con, [sum_con], v
end

function _build_partitioned_constraint(
    model::M,
    con::JuMP.ScalarConstraint{T, S},
    method::PSplit
) where {M <: JuMP.AbstractModel, T, S <: Union{_MOI.Interval, _MOI.EqualTo}}
    val_type = JuMP.value_type(M)
    p = length(method.partition)
    part_con_lt = Vector{JuMP.AbstractConstraint}(undef, p)
    part_con_gt = Vector{JuMP.AbstractConstraint}(undef, p)
    #let [_, 1] be the upper bound and [_, 2] be the lower bound
    _, constant = _build_partitioned_expression(con.func, method.partition[p]) 
    v = [@variable(
        model, 
        base_name = "v_$(hash(con))_$(i)_$(j)"
        ) for i in 1:p, j in 1:2]
    for i in 1:p
        func, _= _build_partitioned_expression(con.func, method.partition[i])
        part_con_lt[i] = JuMP.build_constraint(error, 
        func - v[i,1], MOI.LessThan(zero(val_type))
        )
        part_con_gt[i] = JuMP.build_constraint(error, 
        -func - v[i,2], MOI.LessThan(zero(val_type))
        )
        _bound_auxiliary(model, v[i,1], func, method)
        _bound_auxiliary(model, v[i,2], -func, method)
    end
    set_values = _set_values(con.set)
    sum_con_lt = JuMP.build_constraint(error, sum(v[i,1] for i in 1:p), 
    MOI.LessThan((set_values[2] - constant))
    )
    sum_con_gt = JuMP.build_constraint(error, sum(v[i,2] for i in 1:p), 
    MOI.LessThan(-set_values[1] + constant)
     )
    return vcat(part_con_lt, part_con_gt), [sum_con_lt, sum_con_gt], vec(v)
end
function _build_partitioned_constraint(
    model::M,
    con::JuMP.VectorConstraint{T, S, R},
    method::PSplit
) where {M <: JuMP.AbstractModel, T, S <: _MOI.Nonpositives, R}
    p = length(method.partition)
    d = con.set.dimension
    v = [@variable(
        model, 
        base_name = "v_$(hash(con))_$(i)_$(j)"
        ) for i in 1:p, j in 1:d]
    part_con = Vector{JuMP.AbstractConstraint}(undef, p)
    constants = Vector{Number}(undef, d)
    for i in 1:p
        part_expr = [_build_partitioned_expression(con.func[j],
        method.partition[i]) for j in 1:d
        ]
        func = JuMP.@expression(model, [j = 1:d], part_expr[j][1])
        constants .= [part_expr[j][2] for j in 1:d]
        part_con[i] = JuMP.build_constraint(error, 
        func - v[i,:], _MOI.Nonpositives(d)
        )
        for j in 1:d
            _bound_auxiliary(model, v[i,j], func[j], method)
        end
    end
    new_func = JuMP.@expression(model,[j = 1:d], 
    sum(v[i,j] for i in 1:p) + constants[j]
    )
    sum_con = JuMP.build_constraint(error, new_func, _MOI.Nonpositives(d))
    return part_con, [sum_con], vec(v)
end

function _build_partitioned_constraint(
    model::M,
    con::JuMP.VectorConstraint{T, S, R},
    method::PSplit
) where {M <: JuMP.AbstractModel, T, S <: _MOI.Nonnegatives, R}
    p = length(method.partition)
    d = con.set.dimension
    v = [@variable(
        model, 
        base_name = "v_$(hash(con))_$(i)_$(j)"
        ) for i in 1:p, j in 1:d]
    part_con = Vector{JuMP.AbstractConstraint}(undef, p)
    constants = Vector{Number}(undef, d)
    for i in 1:p
        part_expr = [
            _build_partitioned_expression(con.func[j], method.partition[i]) 
            for j in 1:d
        ]
        func = JuMP.@expression(model, [j = 1:d], -part_expr[j][1])
        constants .= [-part_expr[j][2] for j in 1:d]
        part_con[i] = JuMP.build_constraint(error, func - v[i,:], _MOI.Nonpositives(d))
        for j in 1:d
            _bound_auxiliary(model, v[i,j], func[j], method)
        end
    end
    new_func = JuMP.@expression(model,[j = 1:d], 
    sum(v[i,j] for i in 1:p) + constants[j]
    )
    sum_con = JuMP.build_constraint(error,new_func,_MOI.Nonpositives(d))
    return part_con, [sum_con], vec(v)
end

function _build_partitioned_constraint(
    model::M,
    con::JuMP.VectorConstraint{T, S, R},
    method::PSplit
) where {M <: JuMP.AbstractModel, T, S <: _MOI.Zeros, R}
    p = length(method.partition)
    d = con.set.dimension
    part_con_np = Vector{JuMP.AbstractConstraint}(undef, p)  # nonpositive (≤ 0)
    part_con_nn = Vector{JuMP.AbstractConstraint}(undef, p)  # nonnegative (≥ 0)
    v = [@variable(
        model, 
        base_name = "v_$(hash(con))_$(i)_$(j)_$(k)"
        ) for i in 1:p, j in 1:d, k in 1:2
    ]
    constants = Vector{Number}(undef, d)
    for i in 1:p
        part_expr = [
            _build_partitioned_expression(con.func[j], method.partition[i]) 
            for j in 1:d
        ]
        func = JuMP.@expression(model, [j = 1:d], part_expr[j][1])        
        constants .= [part_expr[j][2] for j in 1:d]
        part_con_np[i] = JuMP.build_constraint(error, 
        func - v[i,:,1], _MOI.Nonpositives(d)
        )
        part_con_nn[i] = JuMP.build_constraint(error, 
        -func - v[i,:,2], _MOI.Nonpositives(d)
        )
        for j in 1:d
            _bound_auxiliary(model, v[i,j,1], func[j], method)
            _bound_auxiliary(model, v[i,j,2], -func[j], method)
        end
    end
    new_func_np = JuMP.@expression(model,[j = 1:d], 
    sum(v[i,j,1] for i in 1:p) + constants[j]
    )
    new_func_nn = JuMP.@expression(model,[j = 1:d], 
    -sum(v[i,j,2] for i in 1:p) - constants[j]
    )
    sum_con_np = JuMP.build_constraint(error, 
    new_func_np, _MOI.Nonpositives(d)
    )
    sum_con_nn = JuMP.build_constraint(error, 
    new_func_nn, _MOI.Nonpositives(d)
    )
    return vcat(part_con_np, part_con_nn), vcat(sum_con_np, sum_con_nn), vec(v)
end

################################################################################
#                          FALLBACK WARNING DISPATCHES
################################################################################

# Generic fallback for _build_partitioned_expression
function _build_partitioned_expression(
    expr::F,
    ::Vector{<:JuMP.AbstractVariableRef}
) where F
    error("PSplit: _build_partitioned_expression not implemented 
    for expression type $F.")
end

# Generic fallback for _bound_auxiliary
function _bound_auxiliary(
    ::JuMP.AbstractModel,
    v::JuMP.AbstractVariableRef,
    func::F,
    ::PSplit
) where F
    error("PSplit: _bound_auxiliary not implemented for function 
    type $F.")
end