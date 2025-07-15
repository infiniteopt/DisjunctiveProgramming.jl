#TODO: Detect nonseperable constraints and throw error
#TODO: Make NL work for all other constraints (LessThan works at the moment.)

function _build_partitioned_expression(
    expr::JuMP.GenericAffExpr,
    partition_variables::Vector{JuMP.VariableRef},
    ::JuMP.ScalarConstraint
)
    new_affexpr = AffExpr(0.0, Dict{JuMP.VariableRef,Float64}())
    for var in partition_variables
        add_to_expression!(new_affexpr, coefficient(expr, var), var) 
    end

    return new_affexpr, 0
end

function _build_partitioned_expression(
    expr::JuMP.GenericQuadExpr,
    partition_variables::Vector{JuMP.VariableRef},
    ::JuMP.ScalarConstraint
)
    
    new_quadexpr = QuadExpr(0.0, Dict{JuMP.VariableRef,Float64}())
    for var in partition_variables
        add_to_expression!(new_quadexpr, get(expr.terms, JuMP.UnorderedPair(var, var), 0.0), var,var) 
        add_to_expression!(new_quadexpr, coefficient(expr, var), var) 
    end

    return new_quadexpr, 0
end

function _build_partitioned_expression(
    expr::JuMP.VariableRef,
    partition_variables::Vector{JuMP.VariableRef},
    ::JuMP.ScalarConstraint
)
    if expr in partition_variables
        return expr, 0
    else
        return 0, 0
    end
end

function _build_partitioned_expression(
    expr::Number,
    partition_variables::Vector{JuMP.VariableRef},
    ::JuMP.ScalarConstraint
    )
    return expr, 0
end

function contains_only_partition_variables(
    expr::JuMP.VariableRef,
    partition_variables::Vector{JuMP.VariableRef}
)
    return expr in partition_variables
end

function contains_only_partition_variables(
    expr::Number,
    partition_variables::Vector{JuMP.VariableRef}
)
    return true
end

#Helper functions for the nonlinear case.
function contains_only_partition_variables(
    expr::Union{JuMP.NonlinearExpr}, 
    partition_variables::Vector{JuMP.VariableRef}
)
    return all(contains_only_partition_variables(arg, partition_variables) for arg in expr.args)
end


function _build_partitioned_expression(
    expr::JuMP.NonlinearExpr,
    partition_variables::Vector{JuMP.VariableRef},
    con::JuMP.ScalarConstraint
)
    if expr.head in (:+, :-)
        rhs = get(filter(x -> isa(x, Number), expr.args), 1, 0.0)
        if expr.head == :+
            rhs = -rhs
        end
        new_func = _nonlinear_recursion(expr, partition_variables, con) + rhs
    else
        new_func = _nonlinear_recursion(expr, partition_variables, con)
        rhs = 0.0
    end
    return new_func, rhs
end

function _nonlinear_recursion(
    expr::Union{JuMP.GenericAffExpr, JuMP.VariableRef, JuMP.GenericQuadExpr, Number},
    partition_variables::Vector{JuMP.VariableRef},
    con::JuMP.ScalarConstraint
)
    new_func, _ = _build_partitioned_expression(expr, partition_variables, con)
    return new_func
end


function _nonlinear_recursion(
    expr::JuMP.NonlinearExpr,
    partition_variables::Vector{JuMP.VariableRef},
    con::JuMP.ScalarConstraint,
    )
    if expr.head in (:+, :-)
        return JuMP.NonlinearExpr(
            expr.head,
            (_nonlinear_recursion(arg, partition_variables, con) for arg in expr.args)...
        )
    end
    if contains_only_partition_variables(expr, partition_variables)
        return expr
    else
        return 0
    end
end


function _bound_auxiliary(
    model::JuMP.AbstractModel,
    v::JuMP.VariableRef,
    func::JuMP.GenericAffExpr,
    method::PSplit
)   
    lower_bound = 0
    upper_bound = 0
    for (var, coeff) in func.terms
        if var != v
            JuMP.is_binary(var) && continue
            if coeff > 0
                lower_bound += coeff * variable_bound_info(var)[1]
                upper_bound += coeff * variable_bound_info(var)[2]
            else
                lower_bound += coeff * variable_bound_info(var)[2]
                upper_bound += coeff * variable_bound_info(var)[1]
            end
        end
    end
    JuMP.set_lower_bound(v, lower_bound)
    JuMP.set_upper_bound(v, upper_bound)
end    

function _bound_auxiliary(
    model::JuMP.AbstractModel,
    v::JuMP.VariableRef,
    func::JuMP.VariableRef,
    method::PSplit
) 
    if func != v
        lower_bound = variable_bound_info(func)[1]
        upper_bound = variable_bound_info(func)[2]
        JuMP.set_lower_bound(v, lower_bound)
        JuMP.set_upper_bound(v, upper_bound)
    else
        JuMP.set_lower_bound(v,0)
        JuMP.set_upper_bound(v,0)
    end
end

function _bound_auxiliary(
    model::JuMP.AbstractModel,
    v::JuMP.VariableRef,
    func::Union{JuMP.NonlinearExpr, JuMP.QuadExpr, Number},
    method::PSplit
) 
end

requires_variable_bound_info(method::PSplit) = true

function set_variable_bound_info(vref::JuMP.AbstractVariableRef, ::PSplit)
    if !has_lower_bound(vref) || !has_upper_bound(vref)
        error("Variable $vref must have both lower and upper bounds defined when using the PSplit reformulation.")
    else
        lb = min(0, lower_bound(vref))
        ub = max(0, upper_bound(vref))
    end
    return lb, ub
end

#DONE WITH NL
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: _MOI.LessThan}
    p = length(method.partition)
    v = [@variable(model) for _ in 1:p]
    _, rhs = _build_partitioned_expression(con.func, method.partition[p], con)
    reform_con = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    for i in 1:p
        func, _ = _build_partitioned_expression(con.func, method.partition[i], con)
        reform_con[i] = JuMP.build_constraint(error, func - v[i], MOI.LessThan(0.0))
        _bound_auxiliary(model, v[i], func, method)
    end
    reform_con[end] = JuMP.build_constraint(error, sum(v[i] * bvref for i in 1:p) - (con.set.upper + rhs) * bvref, MOI.LessThan(0.0))
    return reform_con
end
#TODO: Update with NL
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: _MOI.GreaterThan}
    p = length(method.partition)
    reform_con = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    v = [@variable(model) for _ in 1:p]
    _, rhs = _build_partitioned_expression(con.func, method.partition[p], con)
    
    for i in 1:p
        func, _ = -_build_partitioned_expression(con.func, method.partition[i], con)
        reform_con[i] = JuMP.build_constraint(error, func + v[i], MOI.LessThan(0.0))
        _bound_auxiliary(model, v[i], func, method)
    end
    reform_con[end] = JuMP.build_constraint(error, -sum(v[i] * bvref for i in 1:p) + (con.set.lower - rhs) * bvref, MOI.LessThan(0.0))
    return reform_con
end
#TODO: Update with NL
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: Union{_MOI.Interval, _MOI.EqualTo}}
    p = length(method.partition)
    reform_con_lt = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    reform_con_gt = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    #let [_, 1] be the lower bound and [_, 2] be the upper bound
    _, rhs = _build_partitioned_expression(con.func, method.partition[p], con) 
    v = @variable(model, [1:p, 1:2])
    for i in 1:p
        func, _= _build_partitioned_expression(con.func, method.partition[i], con)
        reform_con_lt[i] = JuMP.build_constraint(error, func - v[i,1], MOI.LessThan(0.0))
        reform_con_gt[i] = JuMP.build_constraint(error, -func + v[i,2], MOI.LessThan(0.0))
        _bound_auxiliary(model, v[i,1], func, method)
        _bound_auxiliary(model, v[i,2], func, method)
    end
    set_values = _set_values(con.set)
    reform_con_lt[end] = JuMP.build_constraint(error, sum(v[i,1] * bvref for i in 1:p) - (set_values[2] - rhs) * bvref, MOI.LessThan(0.0))
    reform_con_gt[end] = JuMP.build_constraint(error, -sum(v[i,2] * bvref for i in 1:p) + (set_values[1] - rhs) * bvref, MOI.LessThan(0.0))
    #TODO: how do i avoid the vcat?
    return vcat(reform_con_lt, reform_con_gt)
end
#TODO: how do i avoid the vcat?
#TODO: Update with NL
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: Union{_MOI.Nonpositives,_MOI.Nonnegatives, _MOI.Zeros}, R}
    p = length(method.partition)
    d = con.set.dimension
    v = @variable(model, [1:p,1:d])
    reform_con = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    for i in 1:p
        func, _ = JuMP.@expression(model, [j = 1:d], _build_partitioned_expression(con.func[j], method.partition[i], con) - v[i,j])
        reform_con[i] = JuMP.build_constraint(error, func, con.set)
        for j in 1:d
            _bound_auxiliary(model, v[i,j], func[j], method)
        end
    end
    new_func = JuMP.@expression(model,[j = 1:d], sum(v[i,j] * bvref for i in 1:p) + JuMP.constant(con.func[j])*bvref)
    reform_con[end] = JuMP.build_constraint(error, new_func, con.set)
    return vcat(reform_con)
end