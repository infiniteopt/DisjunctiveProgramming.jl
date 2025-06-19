################################################################################
#                              MULTIPLE BIG-M VALUES
################################################################################ 
function _M_subproblems(
    model::JuMP.AbstractModel, 
    obj_ref::Vector{ConstraintRef},
    constraint_ref::Vector{ConstraintRef},
    method::MBM
)
    M = zeros(length(obj_ref))
    subproblem = Model()
    var_map = Dict{VariableRef,VariableRef}()
    for v in all_variables(model)
        var_map[v] = @variable(subproblem, base_name = name(v))
    end
    j = 0

    for oref in new_refs
        j +=1
        obj = constraitn_object(oref)
        lhs = obj.func       # Original LHS expression (e.g., x)

        if obj.set isa MOI.LessThan
            rhs = obj.set.upper  # For ≤ constraints
        elseif obj.set isa MOI.GreaterThan
            rhs = obj.set.lower  # For ≥ constraints
        elseif obj.set isa MOI.EqualTo
            rhs = obj.set.value  # For == constraints
        end


        println("LHS: $lhs, RHS: $rhs")

        @objective(subproblem, Max, lhs - rhs)
        constraint_refs = _indicator_to_constraints(model)[constraint_ref]
        constraint_objects = [constraint_object(cref) for cref in constraint_refs]
        for cref in constraint_objects
            substituted_func = substitute(cref.func, var_map)
            @constraint(subproblem, substituted_func ∈ cref.set)
        end
        optimize!(subproblem)

        if JuMP.termination_status(subproblem) == MOI.OPTIMAL && JuMP.has_values(subproblem) && JuMP.primal_status(subproblem) == MOI.FEASIBLE_POINT
            if objective_value(subproblem) >= 0
                M[j] = objective_value(subproblem)
            else
                M[j] = 0  # If the objective is negative, set M to 0
            end
        end
    end
    return M
end
    
function _reformulate_disjunct(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::Vector{},
    otherlvref::Vector{},
    method::MBM
    )
    #reformulate each constraint and add to the model
    bvref = binary_variable(lvref)
    otherbvref = [binary_variable(i) for i in otherlvref] #binary variable in MINLP
    !haskey(_indicator_to_constraints(model), lvref) && return #skip if disjunct is empty
    # Reformulate each constraint in the disjunct
    for cref in _indicator_to_constraints(model)[lvref]
        con = JuMP.constraint_object(cref)
        append!(ref_cons, reformulate_disjunct_constraint(model, con, lvref, otherbvref,method))
    end
    return
end

function reformulate_disjunction(model::JuMP.AbstractModel, disj::Disjunction, method::MBM)
    ref_cons = Vector{JuMP.AbstractConstraint}() #store reformulated constraints
    for d in disj.indicators #d indicator for the GDP (This will be the objec value of the subproblem)
        c = [x for x in disj.indicators if x != d] 
        println(typeof(c))
        _reformulate_disjunct(model, ref_cons, d, c, method)
    end
    return ref_cons
end

# Extend reformulate_disjunct_constraint
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bvref::Vector{},
    otherbvref::Vector{},
    method::MBM
) where {T, S <: _MOI.LessThan}
    M = _M_subproblems(model, bvref, otherbvref, method)
    new_func = JuMP.@expression(model, con.func - sum(M[i] * otherbvref[i] for i in 1:length(M)))
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

function substitute_variables(expr::AbstractJuMPScalar, var_map)
    return substitute(expr, var_map)
end