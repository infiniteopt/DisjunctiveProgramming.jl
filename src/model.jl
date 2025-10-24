################################################################################
#                              GDP MODEL
################################################################################
# Enables the use of parametric typing in the GDPModel function
struct GDPModel{M, V, C} end

"""
    GDPModel([optimizer]; [kwargs...])::JuMP.Model

    GDPModel{T}([optimizer]; [kwargs...])::JuMP.GenericModel{T}

    GDPModel{M <: JuMP.AbstractModel, VrefType, CrefType}([optimizer], [args...]; [kwargs...])::M

The core model object for building general disjunction programming models.
"""
function GDPModel{M, V, C}(
    args...; 
    kwargs...
    ) where {M <: JuMP.AbstractModel, V <: JuMP.AbstractVariableRef, C}
    model = M(args...; kwargs...)
    model.ext[:GDP] = GDPData{M, V, C}()
    JuMP.set_optimize_hook(model, _optimize_hook)
    return model
end
function GDPModel{T}(args...; kwargs...) where {T}
    return GDPModel{
        JuMP.GenericModel{T}, 
        JuMP.GenericVariableRef{T}, 
        JuMP.ConstraintRef
        }(args...; kwargs...)
end
function GDPModel(args...; kwargs...)
    return GDPModel{
        JuMP.Model, 
        JuMP.VariableRef, 
        JuMP.ConstraintRef
        }(args...; kwargs...)
end

# Define what should happen to solve a GDPModel
# See https://github.com/jump-dev/JuMP.jl/blob/9ea1df38fd320f864ab4c93c78631d0f15939c0b/src/JuMP.jl#L718-L745
function _optimize_hook(
    model::JuMP.AbstractModel; 
    gdp_method::AbstractSolutionMethod = BigM(),
    kwargs...
    ) # can add more kwargs if wanted
    if !_ready_to_optimize(model) || _solution_method(model) != gdp_method
        reformulate_model(model, gdp_method)
    end
    return JuMP.optimize!(model; ignore_optimize_hook = true, kwargs...)
end

################################################################################
#                              GDP DATA
################################################################################
"""
    gdp_data(model::JuMP.AbstractModel)::GDPData

Extract the [`GDPData`](@ref) from a `GDPModel`.
"""
function gdp_data(model::JuMP.AbstractModel)
    is_gdp_model(model) || error("Model does not contain GDP data.")
    return model.ext[:GDP]
end

"""
    is_gdp_model(model::JuMP.AbstractModel)::Bool

Return if `model` was created via the [`GDPModel`](@ref) constructor.
"""
function is_gdp_model(model::JuMP.AbstractModel)
    return haskey(model.ext, :GDP)
end

# Create accessors for GDP data fields
_logical_variables(model::JuMP.AbstractModel) = gdp_data(model).logical_variables
_logical_constraints(model::JuMP.AbstractModel) = gdp_data(model).logical_constraints
_disjunct_constraints(model::JuMP.AbstractModel) = gdp_data(model).disjunct_constraints
_disjunctions(model::JuMP.AbstractModel) = gdp_data(model).disjunctions
_exactly1_constraints(model::JuMP.AbstractModel) = gdp_data(model).exactly1_constraints
_indicator_to_binary(model::JuMP.AbstractModel) = gdp_data(model).indicator_to_binary
_indicator_to_constraints(model::JuMP.AbstractModel) = gdp_data(model).indicator_to_constraints
_constraint_to_indicator(model::JuMP.AbstractModel) = gdp_data(model).constraint_to_indicator
_reformulation_variables(model::JuMP.AbstractModel) = gdp_data(model).reformulation_variables
_reformulation_constraints(model::JuMP.AbstractModel) = gdp_data(model).reformulation_constraints
_variable_bounds(model::JuMP.AbstractModel) = gdp_data(model).variable_bounds
_solution_method(model::JuMP.AbstractModel) = gdp_data(model).solution_method # Get the current solution method
_ready_to_optimize(model::JuMP.AbstractModel) = gdp_data(model).ready_to_optimize # Determine if the model is ready to call `optimize!` without a optimize hook

# Update the ready_to_optimize field
function _set_ready_to_optimize(model::JuMP.AbstractModel, is_ready::Bool)
    gdp_data(model).ready_to_optimize = is_ready
    return
end

# Set the solution method
function _set_solution_method(model::JuMP.AbstractModel, method::AbstractSolutionMethod)
    gdp_data(model).solution_method = method
    return
end
