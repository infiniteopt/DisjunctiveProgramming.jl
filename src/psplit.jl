#TODO: If the constraint is Nonlinear -> Throw a warning
#TODO: Fix vectors in general

function _build_partitioned_expression(
    expr::JuMP.GenericAffExpr,
    partition_variables::Vector{JuMP.VariableRef}
)
    constant = JuMP.constant(expr)
    new_affexpr = AffExpr(0.0, Dict{JuMP.VariableRef,Float64}())
    for var in partition_variables
        add_to_expression!(new_affexpr, coefficient(expr, var), var) 
    end
    return new_affexpr, constant
end

function _build_partitioned_expression(
    expr::JuMP.GenericQuadExpr,
    partition_variables::Vector{JuMP.VariableRef}
)
    new_quadexpr = QuadExpr(0.0, Dict{JuMP.VariableRef,Float64}())
    constant = JuMP.constant(expr)
    for var in partition_variables
        add_to_expression!(new_quadexpr, get(expr.terms, JuMP.UnorderedPair(var, var), 0.0), var,var) 
        add_to_expression!(new_quadexpr, coefficient(expr, var), var) 
    end

    return new_quadexpr, constant
end

function _build_partitioned_expression(
    expr::JuMP.VariableRef,
    partition_variables::Vector{JuMP.VariableRef}
)
    if expr in partition_variables
        return expr, 0
    else
        return 0, 0
    end
end

function _build_partitioned_expression(
    expr::Number,
    partition_variables::Vector{JuMP.VariableRef}
)
    return expr, 0
end


function _build_partitioned_expression(
    expr::JuMP.NonlinearExpr,
    partition_variables::Vector{JuMP.VariableRef}
)
    if expr.head in (:+, :-)
        constant = get(filter(x -> isa(x, Number), expr.args), 1, 0.0)
        if expr.head == :+
            constant = -constant
        end
        new_func = _nonlinear_recursion(expr, partition_variables) + constant
    else
        new_func = _nonlinear_recursion(expr, partition_variables)
        constant = 0.0
    end
    return new_func, constant
end

function contains_only_partition_variables(
    expr::Union{JuMP.GenericAffExpr,JuMP.GenericQuadExpr},
    partition_variables::Vector{JuMP.VariableRef}
)
    for (var, _) in expr.terms
        var in partition_variables || return false
    end
    return true
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

function _nonlinear_recursion(
    expr::Union{JuMP.GenericAffExpr, JuMP.VariableRef, JuMP.GenericQuadExpr, Number},
    partition_variables::Vector{JuMP.VariableRef}
)
    new_func, _ = _build_partitioned_expression(expr, partition_variables)
    return new_func
end


function _nonlinear_recursion(
    expr::JuMP.NonlinearExpr,
    partition_variables::Vector{JuMP.VariableRef}
    )
    if expr.head in (:+, :-)
        return JuMP.NonlinearExpr(
            expr.head,
            (_nonlinear_recursion(arg, partition_variables) for arg in expr.args)...
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
        lb = lower_bound(vref)
        ub = upper_bound(vref)
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
    _, rhs = _build_partitioned_expression(con.func, method.partition[p])
    reform_con = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    for i in 1:p
        func, _ = _build_partitioned_expression(con.func, method.partition[i])
        reform_con[i] = JuMP.build_constraint(error, func - v[i], MOI.LessThan(0.0))
        _bound_auxiliary(model, v[i], func, method)
    end
    reform_con[end] = JuMP.build_constraint(error, sum(v[i] * bvref for i in 1:p) - (con.set.upper + rhs) * bvref, MOI.LessThan(0.0))
    return reform_con
end
#DONE WITH NL
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: _MOI.GreaterThan}
    p = length(method.partition)
    reform_con = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    v = [@variable(model) for _ in 1:p]
    _, rhs = _build_partitioned_expression(con.func, method.partition[p])
    
    for i in 1:p
        func, _ = _build_partitioned_expression(con.func, method.partition[i])
        reform_con[i] = JuMP.build_constraint(error, -func + v[i], MOI.LessThan(0.0))
        _bound_auxiliary(model, v[i], -func, method)
    end
    reform_con[end] = JuMP.build_constraint(error, -sum(v[i] * bvref for i in 1:p) + (con.set.lower + rhs) * bvref, MOI.LessThan(0.0))
    return reform_con
end

#Works with NL
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: Union{_MOI.Interval, _MOI.EqualTo}}
    p = length(method.partition)
    reform_con_lt = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    reform_con_gt = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    #let [_, 1] be the upper bound and [_, 2] be the lower bound
    _, rhs = _build_partitioned_expression(con.func, method.partition[p]) 
    v = @variable(model, [1:p, 1:2])
    for i in 1:p
        func, _= _build_partitioned_expression(con.func, method.partition[i])
        reform_con_lt[i] = JuMP.build_constraint(error, func - v[i,1], MOI.LessThan(0.0))
        reform_con_gt[i] = JuMP.build_constraint(error, -func + v[i,2], MOI.LessThan(0.0))
        _bound_auxiliary(model, v[i,1], func, method)
        _bound_auxiliary(model, v[i,2], -func, method)
    end
    set_values = _set_values(con.set)
    reform_con_lt[end] = JuMP.build_constraint(error, sum(v[i,1] * bvref for i in 1:p) - (set_values[2] + rhs) * bvref, MOI.LessThan(0.0))
    reform_con_gt[end] = JuMP.build_constraint(error, -sum(v[i,2] * bvref for i in 1:p) + (set_values[1] + rhs) * bvref, MOI.LessThan(0.0))
    #TODO: how do i avoid the vcat?
    return vcat(reform_con_lt, reform_con_gt)
end
#Functions
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: Union{_MOI.Nonpositives}, R}
    p = length(method.partition)
    d = con.set.dimension
    v = @variable(model, [1:p,1:d])
    reform_con = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    constants = Vector{Number}(undef, d)
    for i in 1:p
        #I should be subtracting the constant here.
        partitioned_expressions = [_build_partitioned_expression(con.func[j], method.partition[i]) for j in 1:d]
        func = JuMP.@expression(model, [j = 1:d], partitioned_expressions[j][1] - v[i,j])
        constants .= [-partitioned_expressions[j][2] for j in 1:d]
        reform_con[i] = JuMP.build_constraint(error, func, _MOI.Nonpositives(d))
        for j in 1:d
            _bound_auxiliary(model, v[i,j], func[j], method)
        end
        println("Reformulated constraint $i: ", reform_con[i])
        println("Constants: ", constants)
    end
    new_func = JuMP.@expression(model,[j = 1:d], sum(v[i,j] * bvref for i in 1:p) - constants[j]*bvref)
    println("New function: ", new_func)
    reform_con[end] = JuMP.build_constraint(error, new_func, _MOI.Nonpositives(d))
    return vcat(reform_con)
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: Union{_MOI.Nonnegatives}, R}
    p = length(method.partition)
    d = con.set.dimension
    v = @variable(model, [1:p,1:d])
    reform_con = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    constants = Vector{Number}(undef, d)
    for i in 1:p
        #I should be subtracting the constant here.
        partitioned_expressions = [_build_partitioned_expression(con.func[j], method.partition[i]) for j in 1:d]
        func = JuMP.@expression(model, [j = 1:d], partitioned_expressions[j][1] - v[i,j])
        constants .= [-partitioned_expressions[j][2] for j in 1:d]
        reform_con[i] = JuMP.build_constraint(error, -func, _MOI.Nonpositives(d))
        for j in 1:d
            _bound_auxiliary(model, v[i,j], -func[j], method)
        end
    end
    new_func = JuMP.@expression(model,[j = 1:d], -sum(v[i,j] * bvref for i in 1:p) + constants[j]*bvref)
    reform_con[end] = JuMP.build_constraint(error, new_func, _MOI.Nonpositives(d))
    #TODO: how do i avoid the vcat?
    return vcat(reform_con)
end
#TODO:
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: Union{_MOI.Zeros}, R}
    p = length(method.partition)
    d = con.set.dimension
    reform_con_np = Vector{JuMP.AbstractConstraint}(undef, p + 1)  # nonpositive (≤ 0)
    reform_con_nn = Vector{JuMP.AbstractConstraint}(undef, p + 1)  # nonnegative (≥ 0)
    v = @variable(model, [1:p,1:d,1:2])  # [i,j,1] for ≤, [i,j,2] for ≥
    constants = Vector{Number}(undef, d)
    for i in 1:p
        partitioned_expressions = [_build_partitioned_expression(con.func[j], method.partition[i]) for j in 1:d]
        
        # Nonpositive part: func ≤ 0 → func - v ≤ 0
        func = JuMP.@expression(model, [j = 1:d], partitioned_expressions[j][1] - v[i,j,1])        
        constants .= [partitioned_expressions[j][2] for j in 1:d]
        
        reform_con_np[i] = JuMP.build_constraint(error, func, _MOI.Nonpositives(d))
        reform_con_nn[i] = JuMP.build_constraint(error, -func, _MOI.Nonpositives(d))
        
        for j in 1:d
            _bound_auxiliary(model, v[i,j,1], func[j], method)
            _bound_auxiliary(model, v[i,j,2], -func[j], method)
        end
    end

    # Final constraints: combine auxiliary variables with constants
    new_func_np = JuMP.@expression(model,[j = 1:d], sum(v[i,j,1] * bvref for i in 1:p) + constants[j]*bvref)
    new_func_nn = JuMP.@expression(model,[j = 1:d], -sum(v[i,j,2] * bvref for i in 1:p) + constants[j]*bvref)
    reform_con_np[end] = JuMP.build_constraint(error, new_func_np, _MOI.Nonpositives(d))
    reform_con_nn[end] = JuMP.build_constraint(error, new_func_nn, _MOI.Nonpositives(d))
    return vcat(reform_con_np, reform_con_nn)
end

################################################################################
#                          FALLBACK WARNING DISPATCHES
################################################################################

# Generic fallback for _build_partitioned_expression
function _build_partitioned_expression(
    expr::Any,
    ::Vector{JuMP.VariableRef}
)
    error("PSplit: _build_partitioned_expression not implemented for expression type $(typeof(expr)). Supported types: GenericAffExpr, GenericQuadExpr, VariableRef, Number, NonlinearExpr.")
end

# Generic fallback for contains_only_partition_variables
function contains_only_partition_variables(
    expr::Any,
    ::Vector{JuMP.VariableRef}
)
    error("PSplit: contains_only_partition_variables not implemented for expression type $(typeof(expr)). Supported types: GenericAffExpr, GenericQuadExpr, VariableRef, Number, NonlinearExpr.")
end

# Generic fallback for _nonlinear_recursion
function _nonlinear_recursion(
    expr::Any,
    ::Vector{JuMP.VariableRef}
)
    error("PSplit: _nonlinear_recursion not implemented for expression type $(typeof(expr)). Supported types: GenericAffExpr, GenericQuadExpr, VariableRef, Number, NonlinearExpr.")
end

# Generic fallback for _bound_auxiliary
function _bound_auxiliary(
    ::JuMP.AbstractModel,
    v::JuMP.VariableRef,
    func::Any,
    ::PSplit
)
    @warn "PSplit: _bound_auxiliary not implemented for function type $(typeof(func)). Auxiliary variable bounds may be suboptimal. Supported types: GenericAffExpr, VariableRef."
    # Set default bounds to avoid errors
    JuMP.set_lower_bound(v, -1e6)
    JuMP.set_upper_bound(v, 1e6)
end

# Generic fallback for reformulate_disjunct_constraint (scalar)
function reformulate_disjunct_constraint(
    ::JuMP.AbstractModel,
    con::Any,
    ::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    ::PSplit
)
    error("PSplit: reformulate_disjunct_constraint not implemented for constraint set type $(typeof(con.set)). Supported types: LessThan, GreaterThan, EqualTo, Interval.")
end

# Generic fallback for reformulate_disjunct_constraint (vector)
function reformulate_disjunct_constraint(
    ::JuMP.AbstractModel,
    con::Any,
    ::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    ::PSplit
)
    error("PSplit: reformulate_disjunct_constraint not implemented for vector constraint set type $(typeof(con)). Supported types: VectorConstraint of _MOI.Nonnegatives, _MOI.Nonpositives, _MOI.Zeros.")
end

# Generic fallback for _set_values
function _set_values(set::Any)
    error("PSplit: _set_values not implemented for constraint set type $(typeof(set)). Supported types: EqualTo, Interval.")
end