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
        old_con_ref = LogicalConstraintRef(model, idx)
        new_con_ref = LogicalConstraintRef(new_model, idx)
        c = con_data.constraint
        println("###C####")
        println(c.func)
        expr = _remap_LogicalExpr(c.func, lv_map)
        set = JuMP.moi_set(c)
        new_con = JuMP.ScalarConstraint(expr, set)
        JuMP.add_constraint(new_model, new_con, con_data.name)
        lc_map[old_con_ref] = new_con_ref
        
    end

    return new_model, ref_map
end

function _remap_LogicalExpr(
    expr::JuMP.AbstractJuMPScalar,
    lv_map::Dict{LogicalVariableRef{M}, LogicalVariableRef{M}}
) where {M <: JuMP.AbstractModel}
    new_expr = _replace_variables_in_constraint(expr, lv_map)
    return new_expr
end

function _remap_LogicalExpr(
    exprs::Vector{JuMP.AbstractJuMPScalar},
    lv_map::Dict{LogicalVariableRef{M}, LogicalVariableRef{M}}
) where {M <: JuMP.AbstractModel}
    new_exprs = JuMP.AbstractJuMPScalar[]
    for expr in exprs
        new_expr = _replace_variables_in_constraint(expr, lv_map)
        push!(new_exprs, new_expr)
    end
    return new_exprs
end

function _remap_LogicalExpr(
    lvars::Vector{LogicalVariableRef{M}},
    lv_map::Dict{LogicalVariableRef{M}, LogicalVariableRef{M}}
) where {M <: JuMP.AbstractModel}
    new_lvars = LogicalVariableRef{M}[]
    for lvar in lvars
        push!(new_lvars, lv_map[lvar])
    end
    return new_lvars
end
