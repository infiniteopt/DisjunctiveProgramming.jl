#TODO: Add dead end functions for when something super generic is given.

################################################################################
#               CONSTRAINT, DISJUNCTION, DISJUNCT REFORMULATION
################################################################################
#Reformulates the disjunction using multiple big-M values
function reformulate_disjunction(model::JuMP.AbstractModel, 
    disj::Disjunction,
    method::MBM
    )
    ref_cons = Vector{JuMP.AbstractConstraint}() 
    for d in disj.indicators
        println(typeof(d))
        _reformulate_disjunct(model, ref_cons, d, LogicalVariableRef[x for x in disj.indicators if x != d], method)
    end
    return ref_cons
end
#Reformualates a disjunct the disjunct of interest 
#represented by lvref and the other indicators in conlvref
function _reformulate_disjunct(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef,
    conlvref::Vector{LogicalVariableRef},
    method::AbstractReformulationMethod
    )
    bconref = VariableRef[binary_variable(i) for i in conlvref]
    !haskey(_indicator_to_constraints(model), lvref) && return
    M = Vector{Float64}(undef, length(conlvref))
    for (i,d) in enumerate(conlvref) 
        M[i] = maximum(_maximize_M(model, constraint_object(cref), 
        Vector{DisjunctConstraintRef}(_indicator_to_constraints(model)[d]), method) 
        for cref in _indicator_to_constraints(model)[lvref])
    end
    for cref in _indicator_to_constraints(model)[lvref]
        con = JuMP.constraint_object(cref)
        append!(ref_cons, reformulate_disjunct_constraint(model, con, bconref, M, method))
    end
    return ref_cons
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bconref:: Vector{VariableRef},
    M::Vector{Float64},
    method::MBM
) where {T, S <: _MOI.Nonpositives, R}
    m_sum = sum(M[i] * bconref[i] for i in 1:length(M))
    new_func = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] - m_sum
    )
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bconref:: Vector{VariableRef},
    M::Vector{Float64},
    method::MBM
) where {T, S <: _MOI.Nonnegatives, R}
    m_sum = sum(M[i] * bconref[i] for i in 1:length(M))
    new_func = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] + m_sum
    )
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bconref:: Vector{VariableRef},
    M::Vector{Float64},
    method::MBM
) where {T, S <: _MOI.Zeros, R}
    m_sum = sum(M[i] * bconref[i] for i in 1:length(M))
    upper_expr = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] + m_sum
    )
    lower_expr = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] - m_sum
    )
    upper_con = JuMP.build_constraint(error, upper_expr, MOI.Nonnegatives(con.set.dimension))
    lower_con = JuMP.build_constraint(error, lower_expr, MOI.Nonpositives(con.set.dimension))
    return [upper_con, lower_con]
end


function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bconref:: Vector{VariableRef},
    M::Vector{Float64},
    method::MBM
) where {T, S <: _MOI.LessThan}
    new_func = JuMP.@expression(model, con.func - sum(M[i] * bconref[i] for i in 1:length(M)))
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bconref:: Vector{VariableRef},
    M::Vector{Float64},
    method::MBM
) where {T, S <: _MOI.GreaterThan}
    new_func = JuMP.@expression(model, con.func + sum(M[i] * bconref[i] for i in 1:length(M)))
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bconref::Vector{VariableRef},
    M::Vector{Float64},
    method::MBM
) where {T, S <: _MOI.Interval}
    lower_func = JuMP.@expression(model, con.func - sum(M[i] * bconref[i] for i in 1:length(M)))
    upper_func = JuMP.@expression(model, con.func + sum(M[i] * bconref[i] for i in 1:length(M)))
    
    lower_con = JuMP.build_constraint(error, lower_func, MOI.GreaterThan(con.set.lower))
    upper_con = JuMP.build_constraint(error, upper_func, MOI.LessThan(con.set.upper))
    return [lower_con, upper_con]
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bconref::Vector{VariableRef},
    M::Vector{Float64},
    method::MBM
) where {T, S <: _MOI.EqualTo}
    upper_func = JuMP.@expression(model, con.func - sum(M[i] * bconref[i] for i in 1:length(M)))
    lower_func = JuMP.@expression(model, con.func + sum(M[i] * bconref[i] for i in 1:length(M)))
    
    upper_con = JuMP.build_constraint(error, upper_func, MOI.LessThan(con.set.value))
    lower_con = JuMP.build_constraint(error, lower_func, MOI.GreaterThan(con.set.value))
    return [lower_con, upper_con]
end

################################################################################
#                          MULTIPLE BIG-M REFORMULATION
################################################################################

function _maximize_M(
    model::JuMP.AbstractModel, 
    objective::VectorConstraint{T, S, R}, 
    constraints::Vector{DisjunctConstraintRef}, 
    method::MBM
) where {T, S <: _MOI.Nonpositives, R}
    return maximum(_maximize_M(model, ScalarConstraint(objective.func[i], MOI.LessThan(0.0)), constraints, method) for i in 1:objective.set.dimension)
end

function _maximize_M(
    model::JuMP.AbstractModel, 
    objective::VectorConstraint{T, S, R}, 
    constraints::Vector{DisjunctConstraintRef}, 
    method::MBM
) where {T, S <: _MOI.Nonnegatives, R}
    return maximum(_maximize_M(model, ScalarConstraint(objective.func[i], MOI.GreaterThan(0.0)), constraints, method) for i in 1:objective.set.dimension)
end

function _maximize_M(
    model::JuMP.AbstractModel, 
    objective::VectorConstraint{T, S, R}, 
    constraints::Vector{DisjunctConstraintRef}, 
    method::MBM
) where {T, S <: _MOI.Zeros, R}
    return max(
        maximum(_maximize_M(model, ScalarConstraint(objective.func[i], MOI.GreaterThan(0.0)), constraints, method) for i in 1:objective.set.dimension),
        maximum(_maximize_M(model, ScalarConstraint(objective.func[i], MOI.LessThan(0.0)), constraints, method) for i in 1:objective.set.dimension)
    )
end

function _maximize_M(
    model::JuMP.AbstractModel, 
    objective::ScalarConstraint{T, S}, 
    constraints::Vector{DisjunctConstraintRef}, 
    method::MBM
) where {T, S <: Union{_MOI.LessThan, _MOI.GreaterThan}}
    return _mini_model(model, objective, constraints, method)
end

function _maximize_M(
    model::JuMP.AbstractModel, 
    objective::ScalarConstraint{T, S}, 
    constraints::Vector{DisjunctConstraintRef}, 
    method::MBM
) where {T, S <: _MOI.Interval}
    return max(_mini_model(model, ScalarConstraint(objective.func, MOI.GreaterThan(objective.set.lower)), constraints, method),
    _mini_model(model, ScalarConstraint(objective.func, MOI.LessThan(objective.set.upper)), constraints, method))
end

function _maximize_M(
    model::JuMP.AbstractModel, 
    objective::ScalarConstraint{T, S}, 
    constraints::Vector{DisjunctConstraintRef}, 
    method::MBM
) where {T, S <: _MOI.EqualTo}
    return max(
        _mini_model(model, ScalarConstraint(objective.func, MOI.GreaterThan(objective.set.value)), constraints, method),
        _mini_model(model, ScalarConstraint(objective.func, MOI.LessThan(objective.set.value)), constraints, method)
    )
end

function _maximize_M(
    ::JuMP.AbstractModel, 
    ::F, 
    ::Vector{DisjunctConstraintRef}, 
    ::MBM
) where {F}
    error("This type of constraints and objective constraint has not been implemented for MBM subproblems\nF: $(F)")
end

function _mini_model(
    model::JuMP.AbstractModel, 
    objective::ScalarConstraint{T,S}, 
    constraints::Vector{DisjunctConstraintRef}, 
    method::MBM
) where {T,S <: Union{_MOI.LessThan, _MOI.GreaterThan}}
    sub_model = Model()
    new_vars = Dict{VariableRef, VariableRef}()
    for var in all_variables(model)
        new_vars[var] = @variable(sub_model, base_name= "sub_model_$(JuMP.name(var))")
        if is_fixed(var)
            JuMP.fix(new_vars[var], fix_value(var); force=true)
        end
        if is_integer(var)
            JuMP.set_integer(new_vars[var])
        end
        if has_upper_bound(var)
            set_upper_bound(new_vars[var], upper_bound(var))
        end
        if has_lower_bound(var)
            set_lower_bound(new_vars[var], lower_bound(var))
        end
        if has_start_value(var)
            JuMP.set_start_value(new_vars[var], start_value(var))
        end
    end
    for con in [constraint_object(con) for con in constraints]
        expr = replace_variables_in_constraint(con.func, new_vars)
        @constraint(sub_model, expr * 1.0 in con.set)
    end
    constraint_to_objective(sub_model, objective, new_vars)
    set_optimizer(sub_model, method.optimizer)
    set_silent(sub_model)
    optimize!(sub_model)
    if JuMP.termination_status(sub_model) != MOI.OPTIMAL || !JuMP.has_values(sub_model) || JuMP.primal_status(sub_model) != MOI.FEASIBLE_POINT
        M = 200
    else
        M = objective_value(sub_model)
    end
    return M
end

function _mini_model(
    model::JuMP.AbstractModel, 
    objective::ScalarConstraint{T,S}, 
    constraints::Vector{DisjunctConstraintRef}, 
    method::MBM
) where {T,S <: Union{_MOI.Nonpositives, _MOI.Nonnegatives, _MOI.Zeros, MOI.EqualTo, MOI.Interval}}
    error("This type of constraints and objective constraint has not been implemented for MBM subproblems")
end

################################################################################
#                          CONSTRAINT TO OBJECTIVE
################################################################################
function constraint_to_objective(sub_model::JuMP.AbstractModel,obj::ScalarConstraint{<:AbstractJuMPScalar, MOI.LessThan{Float64}}, new_vars::Dict{VariableRef, VariableRef})
    @objective(sub_model, Max, - obj.set.upper + replace_variables_in_constraint(obj.func, new_vars))
end
function constraint_to_objective(sub_model::JuMP.AbstractModel,obj::ScalarConstraint{<:AbstractJuMPScalar, MOI.GreaterThan{Float64}}, new_vars::Dict{VariableRef, VariableRef})
    @objective(sub_model, Max, - replace_variables_in_constraint(obj.func, new_vars) + obj.set.lower)
end

function constraint_to_objective(sub_model::JuMP.AbstractModel,obj::ScalarConstraint, new_vars::Dict{VariableRef, VariableRef})
    error("This type of constraint is not supported, only greater than and less than constraints are supported with intervals and equalities being converted.")
end

################################################################################
#                          REPLACE VARIABLES IN CONSTRAINT
################################################################################



function replace_variables_in_constraint(fun::GenericVariableRef, var_map::Dict{VariableRef, VariableRef})
    return var_map[fun]
end

function replace_variables_in_constraint(fun::AffExpr, var_map::Dict{VariableRef, VariableRef})
    new_aff = zero(AffExpr)
    for (var, coef) in fun.terms
        new_var = var_map[var]
        add_to_expression!(new_aff, coef, new_var)
    end
    new_aff.constant = fun.constant  
    return new_aff
end

function replace_variables_in_constraint(fun::QuadExpr, var_map::Dict{VariableRef, VariableRef})
    new_quad = zero(QuadExpr)
    for (vars, coef) in fun.terms
        add_to_expression!(new_quad, coef, var_map[vars.a], var_map[vars.b])
    end
    new_aff = replace_variables_in_constraint(fun.aff, var_map)
    add_to_expression!(new_quad, new_aff)
    return new_quad
end

function replace_variables_in_constraint(fun::Number, var_map::Dict{VariableRef, VariableRef})
    return fun
end

function replace_variables_in_constraint(fun::NonlinearExpr, var_map::Dict{VariableRef, VariableRef})
    new_args = Any[replace_variables_in_constraint(arg, var_map) for arg in fun.args]
    return JuMP.NonlinearExpr(fun.head, new_args)
end

function replace_variables_in_constraint(fun::Vector{T}, var_map::Dict{VariableRef, VariableRef}) where T
    return [replace_variables_in_constraint(expr, var_map) for expr in fun]
end

function replace_variables_in_constraint(::F, ::S) where {F, S}
    error("replace_variables_in_constraint not implemented for $(typeof(F)) and $(typeof(S))")
end