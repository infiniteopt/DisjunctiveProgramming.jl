################################################################################
#               CONSTRAINT, DISJUNCTION, DISJUNCT REFORMULATION
################################################################################
#Reformulates the disjunction using multiple big-M values
function reformulate_disjunction(
    model::JuMP.AbstractModel, 
    disj::Disjunction,
    method::MBM
)
    ref_cons = Vector{JuMP.AbstractConstraint}() 
    for d in disj.indicators
        # Make a copy to avoid modifying during iteration
        constraints = copy(_indicator_to_constraints(model)[d])
        for cref in constraints
            con = JuMP.constraint_object(cref)
            if con isa JuMP.ScalarConstraint{<:Any, <:MOI.Interval}
                # Create lower and upper bound constraints
                lower_con = JuMP.build_constraint(error, con.func, 
                    MOI.GreaterThan(con.set.lower))
                upper_con = JuMP.build_constraint(error, con.func, 
                    MOI.LessThan(con.set.upper))
                # Create new disjunct constraints
                JuMP.add_constraint(model,
                    _DisjunctConstraint(lower_con, d))
                JuMP.add_constraint(model,
                    _DisjunctConstraint(upper_con, d))
                JuMP.delete(model, cref)
            end 
        end
    end
    for d in disj.indicators
        method.conlvref = [x for x in disj.indicators if x != d]
        _reformulate_disjunct(model, ref_cons, d, method)
    end
    return ref_cons
end
#Reformualates a disjunct the disjunct of interest 
#represented by lvref and the other indicators in conlvref
function _reformulate_disjunct(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef,
    method::MBM
) 
    method.M = Dict{LogicalVariableRef, JuMP.value_type(typeof(model))}()
    !haskey(_indicator_to_constraints(model), lvref) && return
    bconref = Dict(d => binary_variable(d) for d in method.conlvref)

    constraints = _indicator_to_constraints(model)[lvref]
    filtered_constraints = [c for c in constraints if c isa DisjunctConstraintRef]

    for d in method.conlvref
        d_constraints = _indicator_to_constraints(model)[d]
        disjunct_constraints = [c for c in d_constraints if c isa DisjunctConstraintRef]
        if !isempty(disjunct_constraints)
            method.M[d] = maximum(_maximize_M(model, 
                JuMP.constraint_object(cref), 
                disjunct_constraints,
                method) for cref in filtered_constraints)  
        end
    end
    for cref in filtered_constraints  
        con = JuMP.constraint_object(cref)  
        append!(ref_cons, reformulate_disjunct_constraint(model, con, 
            bconref, method))
    end
    return ref_cons
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,  
    con::Disjunction, 
    bconref::Union{Dict{<:LogicalVariableRef,<:JuMP.AbstractVariableRef},
                   Dict{<:LogicalVariableRef,<:JuMP.GenericAffExpr}},
    method::MBM
)

    ref_cons = reformulate_disjunction(model, con, method)
    new_ref_cons = Vector{JuMP.AbstractConstraint}()
    for ref_con in ref_cons
        append!(new_ref_cons, reformulate_disjunct_constraint(model, ref_con, bconref, method)) 
    end
    return new_ref_cons
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bconref:: Union{Dict{<:LogicalVariableRef,<:JuMP.AbstractVariableRef},
                   Dict{<:LogicalVariableRef,<:JuMP.GenericAffExpr}},
    method::MBM
) where {T, S <: _MOI.Nonpositives, R}
    m_sum = sum(method.M[i] * bconref[i] for i in keys(method.M))
    new_func = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] - m_sum
    )
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end


function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bconref:: Union{Dict{<:LogicalVariableRef,<:JuMP.AbstractVariableRef},
                   Dict{<:LogicalVariableRef,<:JuMP.GenericAffExpr}},
    method::MBM
) where {T, S <: _MOI.Nonnegatives, R}
    m_sum = sum(method.M[i] * bconref[i] for i in keys(method.M))
    new_func = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] + m_sum
    )
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bconref:: Union{Dict{<:LogicalVariableRef,<:JuMP.AbstractVariableRef},
                   Dict{<:LogicalVariableRef,<:JuMP.GenericAffExpr}},
    method::MBM
) where {T, S <: _MOI.Zeros, R}
    m_sum = sum(method.M[i] * bconref[i] for i in keys(method.M))
    upper_expr = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] + m_sum
    )
    lower_expr = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] - m_sum
    )
    upper_con = JuMP.build_constraint(error, upper_expr, 
        MOI.Nonnegatives(con.set.dimension))
    lower_con = JuMP.build_constraint(error, lower_expr, 
        MOI.Nonpositives(con.set.dimension))
    return [upper_con, lower_con]
end


function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bconref:: Union{Dict{<:LogicalVariableRef,<:JuMP.AbstractVariableRef},
                   Dict{<:LogicalVariableRef,<:JuMP.GenericAffExpr}},
    method::MBM
) where {T, S <: _MOI.LessThan}
    new_func = JuMP.@expression(model, 
        con.func - sum(method.M[i] * bconref[i] for i in keys(method.M)))
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bconref:: Union{Dict{<:LogicalVariableRef,<:JuMP.AbstractVariableRef},
                   Dict{<:LogicalVariableRef,<:JuMP.GenericAffExpr}},
    method::MBM
) where {T, S <: _MOI.GreaterThan}
    new_func = JuMP.@expression(model, 
        con.func + sum(method.M[i] * bconref[i] for i in keys(method.M)))
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bconref:: Union{Dict{<:LogicalVariableRef,<:JuMP.AbstractVariableRef},
                   Dict{<:LogicalVariableRef,<:JuMP.GenericAffExpr}},
    method::MBM
) where {T, S <: _MOI.EqualTo}
    upper_func = JuMP.@expression(model, 
        con.func - sum(method.M[i] * bconref[i] for i in keys(method.M)))
    lower_func = JuMP.@expression(model, 
        con.func + sum(method.M[i] * bconref[i] for i in keys(method.M)))
    
    upper_con = JuMP.build_constraint(error, upper_func, 
        MOI.LessThan(con.set.value))
    lower_con = JuMP.build_constraint(error, lower_func, 
        MOI.GreaterThan(con.set.value))
    return [lower_con, upper_con]
end

function reformulate_disjunct_constraint(
    ::JuMP.AbstractModel, 
    ::F, 
    ::Union{Dict{<:LogicalVariableRef,<:JuMP.AbstractVariableRef},
                   Dict{<:LogicalVariableRef,<:JuMP.GenericAffExpr}}, 
    ::MBM
) where {F}
    error("Constraint type $(typeof(F)) is not supported by the " *
          "Multiple Big-M reformulation method.")
end

################################################################################
#                          MULTIPLE BIG-M REFORMULATION
################################################################################
# Dispatches over constraint types to reformulate into >= or <= 
# in order to solve the mini-model
function _maximize_M(
    model::JuMP.AbstractModel, 
    objective::JuMP.VectorConstraint{T, S, R}, 
    constraints::Vector{<:DisjunctConstraintRef}, 
    method::MBM
) where {T, S <: _MOI.Nonpositives, R}
    return maximum(_maximize_M(model, 
        JuMP.ScalarConstraint(objective.func[i], MOI.LessThan(0.0)), 
        constraints, method) for i in 1:objective.set.dimension)
end

function _maximize_M(
    model::JuMP.AbstractModel, 
    objective::JuMP.VectorConstraint{T, S, R}, 
    constraints::Vector{<:DisjunctConstraintRef}, 
    method::MBM
) where {T, S <: _MOI.Nonnegatives, R}
    return maximum(_maximize_M(model, 
        JuMP.ScalarConstraint(objective.func[i], MOI.GreaterThan(0.0)), 
        constraints, method) for i in 1:objective.set.dimension)
end

function _maximize_M(
    model::JuMP.AbstractModel, 
    objective::JuMP.VectorConstraint{T, S, R}, 
    constraints::Vector{<:DisjunctConstraintRef}, 
    method::MBM
) where {T, S <: _MOI.Zeros, R}
    return max(
        maximum(_maximize_M(model, 
            JuMP.ScalarConstraint(objective.func[i], 
                MOI.GreaterThan(0.0)), 
            constraints, method) for i in 1:objective.set.dimension),
        maximum(_maximize_M(model, 
            JuMP.ScalarConstraint(objective.func[i], 
                MOI.LessThan(0.0)), 
            constraints, method) for i in 1:objective.set.dimension)
    )
end

function _maximize_M(
    model::JuMP.AbstractModel, 
    objective::JuMP.ScalarConstraint{T, S}, 
    constraints::Vector{<:DisjunctConstraintRef}, 
    method::MBM
) where {T, S <: Union{_MOI.LessThan, _MOI.GreaterThan}}
    return _mini_model(model, objective, constraints, method)
end

function _maximize_M(
    model::JuMP.AbstractModel, 
    objective::JuMP.ScalarConstraint{T, S}, 
    constraints::Vector{<:DisjunctConstraintRef}, 
    method::MBM
) where {T, S <: _MOI.EqualTo}
    return max(
        _mini_model(model, 
            JuMP.ScalarConstraint(objective.func, 
                MOI.GreaterThan(objective.set.value)), 
            constraints, method),
        _mini_model(model, 
            JuMP.ScalarConstraint(objective.func, 
                MOI.LessThan(objective.set.value)), 
            constraints, method)
    )
end

function _maximize_M(
    ::JuMP.AbstractModel, 
    ::F, 
    ::Vector{<:DisjunctConstraintRef}, 
    ::MBM
) where {F}
    error("This type of constraints and objective constraint has " *
          "not been implemented for MBM subproblems\nF: $(F)")
end

# Solve a mini-model to find the maximum value of the objective 
# function for M value
function _mini_model(
    model::JuMP.AbstractModel, 
    objective::JuMP.ScalarConstraint{T,S}, 
    constraints::Vector{<:DisjunctConstraintRef}, 
    method::MBM
) where {T,S <: Union{_MOI.LessThan, _MOI.GreaterThan}}
    var_type = JuMP.variable_ref_type(model)
    sub_model = _copy_model(model)
    new_vars = Dict{var_type, var_type}()
    for var in JuMP.all_variables(model)
        new_vars[var] = variable_copy(sub_model, var)
    end
    for con in [JuMP.constraint_object(con) for con in constraints]
        expr = replace_variables_in_constraint(con.func, new_vars)
        JuMP.@constraint(sub_model, expr * 1.0 in con.set)
    end
    constraint_to_objective(sub_model, objective, new_vars)
    JuMP.set_optimizer(sub_model, method.optimizer)
    JuMP.set_silent(sub_model)
    JuMP.optimize!(sub_model)
    if JuMP.termination_status(sub_model) != MOI.OPTIMAL || 
       !JuMP.has_values(sub_model) || 
       JuMP.primal_status(sub_model) != MOI.FEASIBLE_POINT
        M = 1e9
    else
        M = JuMP.objective_value(sub_model)
    end
    return M
end
# Catches any constraints that were not reformulated in _maximize_M
# _mini_model requires objective to be >= or <= in order to run
function _mini_model(
    model::JuMP.AbstractModel, 
    objective::JuMP.ScalarConstraint{T,S}, 
    constraints::Vector{C}, 
    method::MBM
) where {T,S <: Union{_MOI.Nonpositives, _MOI.Nonnegatives,_MOI.Zeros, MOI.EqualTo, MOI.Interval}, 
                      C <: Union{DisjunctConstraintRef, DisjunctionRef}}
    error("This type of constraints and objective constraint has " *
          "not been implemented for MBM subproblems")
end

################################################################################
#                          CONSTRAINT TO OBJECTIVE
################################################################################
function constraint_to_objective(
    sub_model::JuMP.AbstractModel,
    obj::JuMP.ScalarConstraint{<:JuMP.AbstractJuMPScalar, MOI.LessThan{T}}, 
    new_vars::Dict{V,K}
) where {T,V <: JuMP.AbstractVariableRef, 
         K <: JuMP.AbstractVariableRef}
    JuMP.@objective(sub_model, Max, 
        - obj.set.upper + 
        replace_variables_in_constraint(obj.func, new_vars))
end
function constraint_to_objective(
    sub_model::JuMP.AbstractModel,
    obj::JuMP.ScalarConstraint{<:JuMP.AbstractJuMPScalar, MOI.GreaterThan{T}}, 
    new_vars::Dict{V,K}
) where {T,V <: JuMP.AbstractVariableRef, 
         K <: JuMP.AbstractVariableRef}
    JuMP.@objective(sub_model, Max, 
        - replace_variables_in_constraint(obj.func, new_vars) + 
        obj.set.lower)
end

function constraint_to_objective(
    sub_model::JuMP.AbstractModel,
    obj::JuMP.ScalarConstraint, 
    new_vars::Dict{V,K}
) where {V, K}
    error("This type of constraint is not supported, only greater " *
          "than and less than constraints are supported with " *
          "intervals and equalities being converted.")
end

################################################################################
#                          REPLACE VARIABLES IN CONSTRAINT
################################################################################

function replace_variables_in_constraint(
    fun:: JuMP.AbstractVariableRef, 
    var_map::Dict{<:JuMP.AbstractVariableRef,<:JuMP.AbstractVariableRef}
)
    return var_map[fun]
end

function replace_variables_in_constraint(
    fun::JuMP.GenericAffExpr, 
    var_map::Dict{<:JuMP.AbstractVariableRef,<:JuMP.AbstractVariableRef}
)
    new_aff = JuMP.zero(JuMP.AffExpr)
    for (var, coef) in fun.terms
        new_var = var_map[var]
        JuMP.add_to_expression!(new_aff, coef, new_var)
    end
    new_aff.constant = fun.constant  
    return new_aff
end

function replace_variables_in_constraint(
    fun::JuMP.GenericQuadExpr, 
    var_map::Dict{<:JuMP.AbstractVariableRef,<:JuMP.AbstractVariableRef}
)
    new_quad = JuMP.zero(JuMP.QuadExpr)
    for (vars, coef) in fun.terms
        JuMP.add_to_expression!(new_quad, coef, 
            var_map[vars.a], var_map[vars.b])
    end
    new_aff = replace_variables_in_constraint(fun.aff, var_map)
    JuMP.add_to_expression!(new_quad, new_aff)
    return new_quad
end

function replace_variables_in_constraint(
    fun::Number, 
    var_map::Dict{<:JuMP.AbstractVariableRef,<:JuMP.AbstractVariableRef}
)
    return fun
end

function replace_variables_in_constraint(
    fun::JuMP.GenericNonlinearExpr, 
    var_map::Dict{<:JuMP.AbstractVariableRef,<:JuMP.AbstractVariableRef}
)
    new_args = Any[replace_variables_in_constraint(arg, var_map) 
                   for arg in fun.args]
    return JuMP.GenericNonlinearExpr(fun.head, new_args)
end

function replace_variables_in_constraint(
    fun::Vector, 
    var_map::Dict{<:JuMP.AbstractVariableRef,<:JuMP.AbstractVariableRef}
) 
    return [replace_variables_in_constraint(expr, var_map) 
            for expr in fun]
end

function replace_variables_in_constraint(
    ::F, 
    ::S
) where {F, S}
    error("replace_variables_in_constraint not implemented for " *
          "$(typeof(F)) and $(typeof(S))")
end