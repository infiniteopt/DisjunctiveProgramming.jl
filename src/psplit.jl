#Extending reformulate_disjunction in order to get all possible variables in the disjuncts
#TODO: Dispatch over Nonlinear expressions
#TODO: Create function to handle bounds of the auxiliary variables (involves solving max/min problem with just variable constraints)
#TODO: Verify we can handle multiple constraints per disjunct (It can for quadratic/linears)
#TODO: Detect nonseperable constraints and throw error
#TODO: Test nonlinear stuff
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: _MOI.LessThan}
   
    reform_con = Vector{JuMP.AbstractConstraint}(undef, length(method.partition) + 1)
    v = [@variable(model) for _ in 1:length(method.partition)]
    
    for i in 1:length(method.partition)
        reform_con[i] = JuMP.build_constraint(error, _build_partitioned_expression(con.func, method.partition[i]) - v[i], MOI.LessThan(0.0))
    end
    reform_con[end] = JuMP.build_constraint(error, sum(v[i] * bvref for i in 1:length(v)) - con.set.upper * bvref, MOI.LessThan(0.0))
    return reform_con
end

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

# function replace_variables_in_constraint(fun::NonlinearExpr, var_map::Dict{VariableRef, VariableRef})
#     new_args = Any[replace_variables_in_constraint(arg, var_map) for arg in fun.args]
#     return JuMP.NonlinearExpr(fun.head, new_args)
# end


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
    expr::JuMP.NonlinearExpr,
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