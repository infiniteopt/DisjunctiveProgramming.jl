#Extending reformulate_disjunction in order to get all possible variables in the disjuncts

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::PSplit
) where {T, S <: _MOI.LessThan}
   
    reform_con = Vector{JuMP.AbstractConstraint}(undef, length(method.partition) + 1)
    v = [@variable(model) for _ in 1:length(method.partition)]
    
    for i in 1:length(method.partition)
        reform_con[i] = JuMP.build_constraint(error, build_partitioned_expression(con.func, method.partition[i]) - v[i], MOI.LessThan(0.0))
    end
    reform_con[end] = JuMP.build_constraint(error, sum(v[i] * bvref for i in 1:length(v)) - con.set.upper * bvref, MOI.LessThan(0.0))
    return reform_con
end

function build_partitioned_expression(
    expr::JuMP.GenericAffExpr,
    partition_variables::Vector{JuMP.VariableRef},
)
    new_affexpr = AffExpr(0.0, Dict{JuMP.VariableRef,Float64}())
    for var in partition_variables
        add_to_expression!(new_affexpr, coefficient(expr, var), var) 
    end

    return new_affexpr
end

function build_partitioned_expression(
    expr::JuMP.GenericQuadExpr,
    partition_variables::Vector{JuMP.VariableRef},
)
    
    new_quadexpr = QuadExpr(0.0, Dict{JuMP.VariableRef,Float64}())
    for var in partition_variables
        add_to_expression!(new_quadexpr, get(expr.terms, JuMP.UnorderedPair(var, var), 0.0), var,var) 
        add_to_expression!(new_quadexpr, coefficient(expr, var), var) 
    end

    return new_quadexpr
end

# function bound_auxiliary_variables(
#     expr::JuMP.GenericAffExpr, 
#     aux_var::JuMP.VariableRef,
#     method::PSplit)
    
#     bound_problem = Model(Gurobi.Optimizer)



    
# end
    