################################################################################
#                                MODEL COPYING
################################################################################
# extentsion point for model copying
function _copy_model(
    model::M
    ) where {M <: JuMP.AbstractModel}
    return M()
end

function JuMP.copy_extension_data(
    data::GDPData{M, V, C, T},
    new_model::JuMP.AbstractModel,
    old_model::JuMP.AbstractModel
) where {M, V, C, T}
    return GDPData{M, V, C}()
end

function copy_full_model(
    model::M
    ) where {M <: JuMP.AbstractModel}
    new_model, ref_map = JuMP.copy_model(model)

    old_gdp = model.ext[:GDP]
    new_gdp = new_model.ext[:GDP]
    var_map = Dict(v => ref_map[v] for v in all_variables(model))
    con_map = Dict(con => ref_map[con] for (F, S) in list_of_constraint_types(model) for con in all_constraints(model, F, S))
    lv_map = Dict{LogicalVariableRef{M}, LogicalVariableRef{M}}()
    lc_map = Dict{LogicalConstraintRef{M}, LogicalConstraintRef{M}}()
    for (idx, var) in old_gdp.logical_variables
        old_var_ref = LogicalVariableRef(model, idx)
        new_var = JuMP.add_variable(new_model, var.variable, var.name)
        lv_map[old_var_ref] = new_var
        
    end

    for (idx, con_data) in old_gdp.logical_constraints
        println(con_data)
    end

    return new_model, ref_map
end

function _remap_LogicalExpr(
    c::ScalarConstraint{_LogicalExpr{M}, S},
    lv_map::Dict{LogicalVariableRef{M}, LogicalVariableRef{M}}
)




end


