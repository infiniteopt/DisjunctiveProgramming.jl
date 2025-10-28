################################################################################
#                              REFORMULATE
################################################################################
"""
    reformulate_model(model::JuMP.AbstractModel, method::AbstractSolutionMethod = BigM())

Reformulate a `GDPModel` using the specified `method`. Prior to reformulation,
all previous reformulation variables and constraints are deleted.
"""
function reformulate_model(model::JuMP.AbstractModel, method::AbstractSolutionMethod = BigM())
    #clear all previous reformulations
    _clear_reformulations(model)
    #reformulate
    _reformulate_disjunctions(model, method)
    _reformulate_logical_constraints(model)
    #set solution method
    _set_solution_method(model, method)
    _set_ready_to_optimize(model, true)
    return
end

function _clear_reformulations(model::JuMP.AbstractModel)
    delete.(model, _reformulation_constraints(model))
    delete.(model, _reformulation_variables(model))
    empty!(gdp_data(model).reformulation_constraints)
    empty!(gdp_data(model).reformulation_variables)
    empty!(gdp_data(model).variable_bounds)
    return
end

################################################################################
#                              DISJUNCTIONS
################################################################################
"""
    requires_exactly1(method::AbstractReformulationMethod)

Return a `Bool` whether `method` requires that `Exactly 1` disjunct be selected 
as true for each disjunction. For new reformulation method types, this should be 
extended to return `true` if such a constraint is required (defaults to `false` otherwise).
"""
requires_exactly1(::AbstractReformulationMethod) = false

"""
    requires_variable_bound_info(method::AbstractReformulationMethod)::Bool

Return a `Bool` whether `method` requires variable bound information accessed 
via [`variable_bound_info`](@ref). This should be extended for new 
[`AbstractReformulationMethod`](@ref) methods if needed (defaults to `false`). 
If a new method does require variable bound information, then 
[`set_variable_bound_info`](@ref) should also be extended.
"""
requires_variable_bound_info(::AbstractReformulationMethod) = false

"""
    set_variable_bound_info(vref, method::AbstractReformulationMethod)::Tuple{<:Number, <:Number}

Returns a tuple of the form `(lower_bound, upper_bound)` which are the bound information needed by 
`method` to reformulate disjunctions. This only needs to be implemented for `methods` where 
`requires_variable_bound_info(method) = true`. These bounds can later be accessed via 
[`variable_bound_info`](@ref).
"""
function set_variable_bound_info end

"""
    variable_bound_info(vref::JuMP.AbstractVariableRef)::Tuple{<:Number, <:Number}

Returns a tuple of the form `(lower_bound, upper_bound)` needed to implement reformulation 
methods. Only works if [`requires_variable_bound_info`](@ref) is implemented.
"""
function variable_bound_info(vref::JuMP.AbstractVariableRef)
   return _variable_bounds(JuMP.owner_model(vref))[vref]
end

# disjunctions
function _reformulate_disjunctions(model::JuMP.AbstractModel, method::AbstractReformulationMethod)
    for (idx, disj) in _disjunctions(model)
        disj.constraint.nested && continue #only reformulate top level disjunctions
        dref = DisjunctionRef(model, idx)
        if requires_exactly1(method) && !haskey(gdp_data(model).exactly1_constraints, dref) &&
            !any(has_logical_complement.(disj.constraint.indicators))
            error("Reformulation method `$method` requires disjunctions where only 1 disjunct is selected, ",
                  "but `exactly1 = false` or none of the logical variables are logical complements ",
                  "for disjunction `$dref`.")
        end
        if requires_variable_bound_info(method)
            for vref in _get_disjunction_variables(model, disj.constraint)
                _variable_bounds(model)[vref] = set_variable_bound_info(vref, method)
            end
        end
        ref_cons = reformulate_disjunction(model, disj.constraint, method)
        for (i, ref_con) in enumerate(ref_cons)
            name = isempty(disj.name) ? "" : string(disj.name,"_$i")
            cref = JuMP.add_constraint(model, ref_con, name)
            push!(_reformulation_constraints(model), cref)
        end
    end
end

# individual disjunctions
"""
    reformulate_disjunction(
        model::JuMP.AbstractModel, 
        disj::Disjunction,
        method::AbstractReformulationMethod
    ) where {T<:Disjunction}

Reformulate a disjunction using the specified `method`. Current reformulation methods include
`BigM`, `Hull`, and `Indicator`. This method can be extended for other reformulation techniques.

The `disj` field is the `ConstraintData` object for the disjunction, stored in the 
`disjunctions` field of the `GDPData` object.
"""
function reformulate_disjunction(model::JuMP.AbstractModel, disj::Disjunction, method::AbstractReformulationMethod)
    ref_cons = Vector{JuMP.AbstractConstraint}() #store reformulated constraints
    for d in disj.indicators
        _reformulate_disjunct(model, ref_cons, d, method)
    end
    return ref_cons
end

# individual disjuncts
function _reformulate_disjunct(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef, 
    method::AbstractReformulationMethod
    )
    #reformulate each constraint and add to the model
    bvref = binary_variable(lvref)
    !haskey(_indicator_to_constraints(model), lvref) && return #skip if disjunct is empty
    for cref in _indicator_to_constraints(model)[lvref]
        con = JuMP.constraint_object(cref)
        append!(ref_cons, reformulate_disjunct_constraint(model, con, bvref, method))
    end
    return
end

"""
    reformulate_disjunct_constraint(
        model::JuMP.AbstractModel,  
        con::JuMP.AbstractConstraint, 
        bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
        method::AbstractReformulationMethod
    )

Extension point for reformulation method `method` to reformulate disjunction constraint `con` over each 
constraint. If `method` needs to specify how to reformulate the entire disjunction, see 
[`reformulate_disjunction`](@ref).
"""
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,  
    con::Disjunction, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::AbstractReformulationMethod
)
    ref_cons = reformulate_disjunction(model, con, method)
    new_ref_cons = Vector{JuMP.AbstractConstraint}()
    for ref_con in ref_cons
        append!(new_ref_cons, reformulate_disjunct_constraint(model, ref_con, bvref, method)) 
    end
    return new_ref_cons
end

# reformulation fallback for individual disjunct constraints
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,  
    con::JuMP.AbstractConstraint, 
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::AbstractReformulationMethod
)
    error("$(typeof(method)) reformulation for constraint $con is not supported yet.")
end

################################################################################
#                       LOGICAL CONSTRAINT REFORMULATION
################################################################################
# all logical constraints
function _reformulate_logical_constraints(model::JuMP.AbstractModel)
    for (_, lcon) in _logical_constraints(model)
        _reformulate_logical_constraint(model, lcon.constraint.func, lcon.constraint.set)
    end
end
# individual logical constraints
function _reformulate_logical_constraint(
    model::JuMP.AbstractModel, 
    func, 
    set::Union{_MOIAtMost, _MOIAtLeast, _MOIExactly}
    )
    return _reformulate_selector(model, func, set)
end
function _reformulate_logical_constraint(model::JuMP.AbstractModel, func, ::MOI.EqualTo{Bool}) # set.value is always true
    return _reformulate_proposition(model, func)
end
