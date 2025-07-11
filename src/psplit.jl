#Extending reformulate_disjunction in order to get all possible variables in the disjuncts

#TODO: TEST Dispatch over Nonlinear expressions
#TODO: Create function to handle bounds of the auxiliary variables (involves solving max/min problem with just variable constraints)
#TODO: Detect nonseperable constraints and throw error
#TODO: Test nonlinear stuff

function _build_partitioned_expression(
    expr::JuMP.GenericAffExpr,
    partition_variables::Vector{JuMP.VariableRef}
)
    new_affexpr = AffExpr(0.0, Dict{JuMP.VariableRef,Float64}())
    for var in partition_variables
        add_to_expression!(new_affexpr, coefficient(expr, var), var) 
    end

    return new_affexpr
end

function _build_partitioned_expression(
    expr::JuMP.GenericQuadExpr,
    partition_variables::Vector{JuMP.VariableRef}
)
    
    new_quadexpr = QuadExpr(0.0, Dict{JuMP.VariableRef,Float64}())
    for var in partition_variables
        add_to_expression!(new_quadexpr, get(expr.terms, JuMP.UnorderedPair(var, var), 0.0), var,var) 
        add_to_expression!(new_quadexpr, coefficient(expr, var), var) 
    end

    return new_quadexpr
end

function _build_partitioned_expression(
    expr::JuMP.VariableRef,
    partition_variables::Vector{JuMP.VariableRef}
)
    if expr in partition_variables
        return expr
    else
        return 0
    end
end

function _build_partitioned_expression(
    expr::Number,
    partition_variables::Vector{JuMP.VariableRef}
)
    return expr
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

# function contains_only_partition_variables(
#     expr::Union{JuMP.GenericAffExpr, JuMP.GenericQuadExpr},
#     partition_variables::Vector{JuMP.VariableRef}

#     return all(contains_only_partition_variables(arg, partition_variables) for arg in expr.terms)
# end

#Helper functions for the nonlinear case.
function contains_only_partition_variables(
    expr::Union{JuMP.NonlinearExpr},
    partition_variables::Vector{JuMP.VariableRef}
)
    return all(contains_only_partition_variables(arg, partition_variables) for arg in expr.args)
end



function _build_partitioned_expression(
    expr::JuMP.NonlinearExpr,
    partition_variables::Vector{JuMP.VariableRef}
)
    if expr.head == :+
        return JuMP.NonlinearExpr(
            :+, 
            (_build_partitioned_expression(arg, partition_variables) for arg in expr.args)...
        )
    end

    if contains_only_partition_variables(expr, partition_variables)
        return expr
    else
        return 0
    end
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: _MOI.LessThan}
    p = length(method.partition)
    v = [@variable(model) for _ in 1:p]
    reform_con = Vector{JuMP.AbstractConstraint}(undef, p + 1)

    reform_con[1:p] = [
        JuMP.build_constraint(error, _build_partitioned_expression(con.func, method.partition[i]) - v[i], MOI.LessThan(0.0)) for i in 1:p
    ]
    reform_con[end] = JuMP.build_constraint(error, sum(v[i] * bvref for i in 1:p) - con.set.upper * bvref, MOI.LessThan(0.0))

    return reform_con
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: _MOI.GreaterThan}
    p = length(method.partition)
    reform_con = Vector{JuMP.AbstractConstraint}(undef, p + 1)
    v = [@variable(model) for _ in 1:p]
    
    reform_con[1:p] = [
        JuMP.build_constraint(error, -_build_partitioned_expression(con.func, method.partition[i]) + v[i], MOI.LessThan(0.0)) for i in 1:p
    ]
    reform_con[end] = JuMP.build_constraint(error, -sum(v[i] * bvref for i in 1:p) + con.set.lower * bvref, MOI.LessThan(0.0))
    return reform_con
end

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
    v = @variable(model, [1:p, 1:2])
    for i in 1:p
        reform_con_lt[i] = JuMP.build_constraint(error, _build_partitioned_expression(con.func, method.partition[i]) - v[i,1], MOI.LessThan(0.0))
        reform_con_gt[i] = JuMP.build_constraint(error, -_build_partitioned_expression(con.func, method.partition[i]) + v[i,2], MOI.LessThan(0.0))
    end
    set_values = _set_values(con.set)
    reform_con_lt[end] = JuMP.build_constraint(error, sum(v[i,1] * bvref for i in 1:p) - set_values[2] * bvref, MOI.LessThan(0.0))
    reform_con_gt[end] = JuMP.build_constraint(error, -sum(v[i,2] * bvref for i in 1:p) + set_values[1] * bvref, MOI.LessThan(0.0))
    #TODO: how do i avoid the vcat?
    return vcat(reform_con_lt, reform_con_gt)
end
#TODO: how do i avoid the vcat?

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
        new_func = JuMP.@expression(model, [j = 1:d], _build_partitioned_expression(con.func[j], method.partition[i]) - v[i,j])
        reform_con[i] = JuMP.build_constraint(error, new_func, con.set)
    end
    new_func = JuMP.@expression(model,[j = 1:d], bvref*sum(v[i,j] for i in 1:p) + JuMP.constant(con.func[j])*bvref)
    reform_con[end] = JuMP.build_constraint(error, new_func, con.set)
    return vcat(reform_con)
end