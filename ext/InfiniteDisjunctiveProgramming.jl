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
function is_parameter(vref::InfiniteOpt.GeneralVariableRef)
    dref = InfiniteOpt.dispatch_variable_ref(vref)
    if typeof(dref) <: Union{InfiniteOpt.DependentParameterRef, InfiniteOpt.IndependentParameterRef, InfiniteOpt.ParameterFunctionRef}
        return true
    else
        return false
    end
end

function DP.requires_disaggregation(vref::InfiniteOpt.GeneralVariableRef)
    return !is_parameter(vref)
end

# Add to InfiniteDisjunctiveProgramming.jl
# Override for affine expressions to handle parameters
function DP._disaggregate_expression(
    model::M,
    aff::JuMP.GenericAffExpr,
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::DP._Hull
    ) where {M <: InfiniteOpt.InfiniteModel}
    # Initialize as QuadExpr instead of AffExpr to handle parameter*binary terms
    new_expr = JuMP.@expression(model, aff.constant*bvref + 0*bvref*bvref)  # Trick to make it QuadExpr
    for (vref, coeff) in aff.terms
        if JuMP.is_binary(vref)
            JuMP.add_to_expression!(new_expr, coeff*vref)
        elseif vref isa InfiniteOpt.GeneralVariableRef && is_parameter(vref)
            # Parameters need perspective function applied (creates quadratic term)
            JuMP.add_to_expression!(new_expr, coeff*vref*bvref)
        elseif !haskey(method.disjunct_variables, (vref, bvref))
            # Non-disaggregated variables
            JuMP.add_to_expression!(new_expr, coeff*vref)
        else
            # Disaggregated variables
            dvref = method.disjunct_variables[vref, bvref]
            JuMP.add_to_expression!(new_expr, coeff*dvref)
        end
    end
    return new_expr
end



function DP.VariableProperties(vref::InfiniteOpt.GeneralVariableRef)
    info = DP.get_variable_info(vref)
    name = JuMP.name(vref)
    set = nothing
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