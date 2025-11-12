module InfiniteDisjunctiveProgramming

import InfiniteOpt, JuMP
import DisjunctiveProgramming as DP

# Extend the public API methods
function DP.InfiniteGDPModel(args...; kwargs...)
    return DP.GDPModel{
        InfiniteOpt.InfiniteModel, 
        InfiniteOpt.GeneralVariableRef, 
        InfiniteOpt.InfOptConstraintRef
        }(args...; kwargs...)
end
DP.InfiniteLogical(prefs...) = DP.Logical(InfiniteOpt.Infinite(prefs...))

# Make necessary extensions for Hull method
function DP.requires_disaggregation(
    vref::Union{InfiniteOpt.GeneralVariableRef, InfiniteOpt.GenericVariableRef})
    if vref.index_type <: InfiniteOpt.InfOptParameter
        return false
    else
        return true
    end
end

function DP.set_variable_bound_info(vref::InfiniteOpt.GeneralVariableRef, ::DP.Hull)
    if !JuMP.has_lower_bound(vref) || !JuMP.has_upper_bound(vref)
        lb = -1e6
        ub = 1e6
    else
        lb = min(0, JuMP.lower_bound(vref))
        ub = max(0, JuMP.upper_bound(vref))
    end
    return lb, ub
end

function DP.VariableProperties(vref::InfiniteOpt.GeneralVariableRef)
    T = JuMP.value_type(InfiniteOpt.InfiniteModel)
    println("EORIGHJREPIUUGERWPIOUHERPIOGEPRGUH")
    # Extract standard info
    info = JuMP.VariableInfo(
        JuMP.has_lower_bound(vref),
        JuMP.has_lower_bound(vref) ? JuMP.lower_bound(vref) : zero(T),
        JuMP.has_upper_bound(vref),
        JuMP.has_upper_bound(vref) ? JuMP.upper_bound(vref) : zero(T),
        JuMP.is_fixed(vref),
        JuMP.is_fixed(vref) ? JuMP.fix_value(vref) : zero(T),
        !isnothing(JuMP.start_value(vref)),
        JuMP.start_value(vref),
        JuMP.is_binary(vref),
        JuMP.is_integer(vref)
    )
    
    name = JuMP.name(vref)
    set = nothing
    
    # Extract variable type (parameter references)
    prefs = InfiniteOpt.parameter_refs(vref)
    var_type = !isempty(prefs) ? InfiniteOpt.Infinite(prefs...) : nothing
    
    return DP.VariableProperties(info, name, set, var_type)
end

function DP._disaggregate_variable(
    model::M, 
    lvref::DP.LogicalVariableRef, 
    vref::InfiniteOpt.GeneralVariableRef, 
    method::DP._Hull) where {M <: InfiniteOpt.InfiniteModel}
    lb, ub = DP.variable_bound_info(vref)
    properties = DP.VariableProperties(vref)
    println("starting")
    dvref = DP.create_variable(model, properties)
    println("completed")
    push!(DP._reformulation_variables(model), dvref)
    #get binary indicator variable
    bvref = DP.binary_variable(lvref)
    #temp storage
    push!(method.disjunction_variables[vref], dvref)
    method.disjunct_variables[vref, bvref] = dvref
    #create bounding constraints
    dvname = JuMP.name(dvref)
    lbname = isempty(dvname) ? "" : "$(dvname)_lower_bound"
    ubname = isempty(dvname) ? "" : "$(dvname)_upper_bound"
    new_con_lb_ref = JuMP.@constraint(model, lb*bvref - dvref <= 0, base_name = lbname)
    new_con_ub_ref = JuMP.@constraint(model, dvref - ub*bvref <= 0, base_name = ubname)
    push!(DP._reformulation_constraints(model), new_con_lb_ref, new_con_ub_ref)
    return dvref
end


# Add necessary @constraint extensions
function JuMP.add_constraint(
    model::InfiniteOpt.InfiniteModel,
    c::JuMP.VectorConstraint{F, S},
    name::String = ""
    ) where {F, S <: DP.AbstractCardinalitySet}
    return DP._add_cardinality_constraint(model, c, name)
end
function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{DP._LogicalExpr{M}, S},
    name::String = ""
    ) where {S, M <: InfiniteOpt.InfiniteModel}
   return DP._add_logical_constraint(model, c, name)
end
function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{DP.LogicalVariableRef{M}, S},
    name::String = ""
    ) where {M <: InfiniteOpt.InfiniteModel, S}
    error("Cannot define constraint on single logical variable, use `fix` instead.")
end
function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{JuMP.GenericAffExpr{C, DP.LogicalVariableRef{M}}, S},
    name::String = ""
    ) where {M <: InfiniteOpt.InfiniteModel, S, C}
    error("Cannot add, subtract, or multiply with logical variables.")
end
function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{JuMP.GenericQuadExpr{C, DP.LogicalVariableRef{M}}, S},
    name::String = ""
    ) where {M <: InfiniteOpt.InfiniteModel, S, C}
    error("Cannot add, subtract, or multiply with logical variables.")
end

# Extend value to work properly
function JuMP.value(vref::DP.LogicalVariableRef{InfiniteOpt.InfiniteModel})
    return JuMP.value(DP.binary_variable(vref)) .>= 0.5
end

end