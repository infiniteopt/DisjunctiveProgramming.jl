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
function DP.requires_disaggregation(vref::InfiniteOpt.GeneralVariableRef)
    if vref.index_type <: InfiniteOpt.InfOptParameter
        return false
    else
        return true
    end
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
    # InfiniteOpt variables don't use variable_in_set in the same way as JuMP
    # For now, we set this to nothing (can be extended if needed)
    set = nothing
    
    # Extract variable type (parameter references)
    prefs = InfiniteOpt.parameter_refs(vref)
    var_type = !isempty(prefs) ? InfiniteOpt.Infinite(prefs...) : nothing
    
    return DP.VariableProperties(info, name, set, var_type)
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