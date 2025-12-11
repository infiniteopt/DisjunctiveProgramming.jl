module InfiniteDisjunctiveProgramming
import JuMP.MOI as _MOI
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

function is_parameter(vref::InfiniteOpt.GeneralVariableRef)
    dref = InfiniteOpt.dispatch_variable_ref(vref)
    if typeof(dref) <: Union{InfiniteOpt.DependentParameterRef, InfiniteOpt.IndependentParameterRef, InfiniteOpt.ParameterFunctionRef, InfiniteOpt.FiniteParameterRef}
        return true
    else
        return false
    end
end

function DP.requires_disaggregation(vref::InfiniteOpt.GeneralVariableRef)
    return !is_parameter(vref)
end



function DP._all_variables(model::InfiniteOpt.InfiniteModel)
    vars = collect(JuMP.all_variables(model))
    derivs = collect(InfiniteOpt.all_derivatives(model))
    return vcat(vars, derivs)
end

function DP._get_constant(expr::JuMP.GenericAffExpr{T, InfiniteOpt.GeneralVariableRef}) where {T}
    constant = JuMP.constant(expr)
    param_expr = zero(typeof(expr))
    for (var, coeff) in expr.terms
        if is_parameter(var)
            JuMP.add_to_expression!(param_expr, coeff, var)
        end
    end
    return constant + param_expr
end

function DP._disaggregate_expression(
    model::M,
    aff::JuMP.GenericAffExpr,
    bvref::Union{JuMP.AbstractVariableRef, JuMP.GenericAffExpr},
    method::DP._Hull
    ) where {M <: InfiniteOpt.InfiniteModel}
    # Build running sum of terms
    terms = Any[aff.constant * bvref]
    
    for (vref, coeff) in aff.terms
        if JuMP.is_binary(vref)
            push!(terms, coeff * vref)
        elseif vref isa InfiniteOpt.GeneralVariableRef && is_parameter(vref)
            push!(terms, coeff * vref * bvref)  # multiply parameter by binary indicator
        elseif !haskey(method.disjunct_variables, (vref, bvref))
            push!(terms, coeff * vref)
        else
            dvref = method.disjunct_variables[vref, bvref]
            push!(terms, coeff * dvref)
        end
    end
    return JuMP.@expression(model, sum(terms))
end

# function _copy_parameters(model::InfiniteOpt.InfiniteModel, new_model::InfiniteOpt.InfiniteModel)
#     p_map = Dict{InfiniteOpt.GeneralVariableRef, InfiniteOpt.GeneralVariableRef}()
#     for param in InfiniteOpt.all_parameters(model)
#         new_param = _copy_parameter(new_model, param)
#         p_map[param] = new_param
#     end
#     return p_map
# end

# # Copy individual parameter based on its dispatch type
# #TODO: Dispatch and over all parameter types
# function _copy_parameter(new_model::InfiniteOpt.InfiniteModel, param::InfiniteOpt.GeneralVariableRef)
#     dref = InfiniteOpt.dispatch_variable_ref(param)
#     if dref isa InfiniteOpt.IndependentParameterRef
#         domain = InfiniteOpt.infinite_domain(param)
#         p = InfiniteOpt.build_parameter(error, domain)
#         return InfiniteOpt.add_parameter(new_model, p, JuMP.name(param))
#     elseif dref isa InfiniteOpt.FiniteParameterRef
#         val = InfiniteOpt.parameter_value(param)
#         p = InfiniteOpt.build_parameter(error, val)
#         return InfiniteOpt.add_parameter(new_model, p, JuMP.name(param))
#     else
#         error("Dependent parameter copying not yet implemented for MBM mini-model")
#     end
# end

# # Remap parameter refs (handles tuples, arrays, and single refs)
# function _remap_parameter_refs(prefs::Tuple, param_map)
#     return Tuple(_remap_parameter_refs(p, param_map) for p in prefs)
# end

# function _remap_parameter_refs(pref::InfiniteOpt.GeneralVariableRef, param_map)
#     return param_map[pref]
# end

# function _remap_parameter_refs(prefs::AbstractArray, param_map)
#     return [_remap_parameter_refs(p, param_map) for p in prefs]
# end

# Extend variable_copy to accept parameter map for infinite variables
# function DP.variable_copy(
#     model::InfiniteOpt.InfiniteModel, 
#     var::InfiniteOpt.GeneralVariableRef,
#     param_map::Dict{InfiniteOpt.GeneralVariableRef, InfiniteOpt.GeneralVariableRef}
# )
#     # If this is a parameter, return the mapped parameter
#     if is_parameter(var)
#         return param_map[var]
#     end
    
#     info = DP.get_variable_info(var)
#     name = JuMP.name(var)
#     prefs = InfiniteOpt.parameter_refs(var)
    
#     if !isempty(prefs)
#         new_prefs = _remap_parameter_refs(prefs, param_map)
#         new_var = JuMP.@variable(model, variable_type = InfiniteOpt.Infinite(new_prefs...), base_name = name)
#         if info.has_lb
#             JuMP.set_lower_bound(new_var, info.lower_bound)
#         end
#         if info.has_ub
#             JuMP.set_upper_bound(new_var, info.upper_bound)
#         end
#         if info.binary
#             JuMP.set_binary(new_var)
#         end
#         if info.integer
#             JuMP.set_integer(new_var)
#         end
#         return new_var
#     else
#         # Finite variable - use standard copy
#         props = DP.VariableProperties(info, name, nothing, nothing)
#         return DP.create_variable(model, props)
#     end
# end

# # Override _mini_model for InfiniteModel
# function DP._mini_model(
#     model::InfiniteOpt.InfiniteModel, 
#     objective::JuMP.ScalarConstraint{T,S}, 
#     constraints::Vector{<:DP.DisjunctConstraintRef}, 
#     method::DP._MBM
# ) where {T, S <: Union{_MOI.LessThan, _MOI.GreaterThan}}
#     var_type = JuMP.variable_ref_type(model)
#     sub_model = DP._copy_model(model)
    
#     # First copy parameters
#     param_map = _copy_parameters(model, sub_model)
    
#     # Combined map for variable/parameter replacement
#     ref_map = Dict{var_type, var_type}()
#     merge!(ref_map, param_map)
    
#     # Copy variables (skip parameters - they're already in the map)
#     for var in JuMP.all_variables(model)
#         if !is_parameter(var)
#             ref_map[var] = variable_copy(sub_model, var, param_map)
#         end
#     end
    
#     # Add constraints with remapped variables
#     for con in [JuMP.constraint_object(c) for c in constraints]
#         expr = DP._replace_variables_in_constraint(con.func, ref_map)
#         JuMP.@constraint(sub_model, expr * 1.0 in con.set)
#     end
    
#     # Set objective
#     DP._constraint_to_objective(sub_model, objective, ref_map)
    
#     JuMP.set_optimizer(sub_model, method.optimizer)
#     JuMP.set_silent(sub_model)
#     JuMP.optimize!(sub_model)
#     if JuMP.termination_status(sub_model) != MOI.OPTIMAL || 
#        !JuMP.has_values(sub_model) || 
#        JuMP.primal_status(sub_model) != MOI.FEASIBLE_POINT
#         M = method.default_M
#     else
#         M = JuMP.objective_value(sub_model)
#     end
#     return M
# end

function DP.VariableProperties(vref::InfiniteOpt.GeneralVariableRef)
    info = DP.get_variable_info(vref)
    name = JuMP.name(vref)
    set = nothing
    prefs = InfiniteOpt.parameter_refs(vref)
    var_type = !isempty(prefs) ? InfiniteOpt.Infinite(prefs...) : nothing
    return DP.VariableProperties(info, name, set, var_type)
end

# Create blank variable with explicit parameter refs
function DP.create_blank_variable(model::InfiniteOpt.InfiniteModel, name::String, prefs::Tuple)
    info = DP._blank_variable_info()
    if isempty(prefs)
        var = JuMP.build_variable(error, info)
    else
        var = JuMP.build_variable(error, info, InfiniteOpt.Infinite(prefs...))
    end
    return JuMP.add_variable(model, var, name)
end

# Create blank variable, inferring parameter refs from a single expression
function DP.create_blank_variable(model::InfiniteOpt.InfiniteModel, name::String, expr)
    prefs = InfiniteOpt.parameter_refs(expr)
    return DP.create_blank_variable(model, name, prefs)
end

# Create blank variable, inferring parameter refs from a vector of expressions
function DP.create_blank_variable(model::InfiniteOpt.InfiniteModel, name::String, exprs::Vector)
    # Collect all unique parameter refs from all expressions
    all_prefs = Set{InfiniteOpt.GeneralVariableRef}()
    for expr in exprs
        for pref in InfiniteOpt.parameter_refs(expr)
            push!(all_prefs, pref)
        end
    end
    return DP.create_blank_variable(model, name, Tuple(all_prefs))
end

# Default: no parameter dependency
function DP.create_blank_variable(model::InfiniteOpt.InfiniteModel, name::String = "")
    return DP.create_blank_variable(model, name, ())
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