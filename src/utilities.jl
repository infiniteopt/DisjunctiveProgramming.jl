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

function copy_gdp_data(
    model::M,
    new_model::M,
    ref_map::GenericReferenceMap
    ) where {M <: JuMP.AbstractModel}

    old_gdp = model.ext[:GDP]
    new_gdp = new_model.ext[:GDP]
    var_map = Dict(v => ref_map[v] for v in all_variables(model))
    lv_map = Dict{LogicalVariableRef{M}, LogicalVariableRef{M}}()
    lc_map = Dict{LogicalConstraintRef{M}, LogicalConstraintRef{M}}()
    disj_map = Dict{DisjunctionRef{M}, DisjunctionRef{M}}()
    disj_con_map = Dict{DisjunctConstraintRef{M}, DisjunctConstraintRef{M}}()
    for (idx, var) in old_gdp.logical_variables
        old_var_ref = LogicalVariableRef(model, idx)
        new_var = JuMP.add_variable(new_model, var.variable, var.name)
        lv_map[old_var_ref] = new_var
    end

    for (idx, lc_data) in old_gdp.logical_constraints
        old_con_ref = LogicalConstraintRef(model, idx)
        new_con_ref = LogicalConstraintRef(new_model, idx)
        c = lc_data.constraint
        expr = _replace_variables_in_constraint(c.func, lv_map)
        new_con = JuMP.build_constraint(error, expr, c.set)
        JuMP.add_constraint(new_model, new_con, lc_data.name)
        lc_map[old_con_ref] = new_con_ref
    end

    for (idx, disj_con_data) in old_gdp.disjunct_constraints
        old_constraint = disj_con_data.constraint
        old_dc_ref = DisjunctConstraintRef(model, idx)
        old_indicator = old_gdp.constraint_to_indicator[old_dc_ref]
        new_indicator = lv_map[old_indicator]
        new_expr = _replace_variables_in_constraint(old_constraint.func, 
        var_map
        )
        new_con = JuMP.build_constraint(error, new_expr, 
        old_constraint.set, Disjunct(new_indicator)
        )
        new_dc_ref = JuMP.add_constraint(new_model, new_con, disj_con_data.name)
        disj_con_map[old_dc_ref] = new_dc_ref
    end

    for (idx, disj_data) in old_gdp.disjunctions
        old_disj = disj_data.constraint
        new_indicators = [_replace_variables_in_constraint(indicator, lv_map) 
        for indicator in old_disj.indicators
            ]
        new_disj = Disjunction(new_indicators, old_disj.nested)
        disj_map[DisjunctionRef(model, idx)] = DisjunctionRef(new_model, idx)
        new_gdp.disjunctions[idx] = ConstraintData(new_disj, disj_data.name)
    end
    
    for (d_ref, lc_ref) in old_gdp.exactly1_constraints
        new_lc_ref = lc_map[lc_ref]
        new_d_ref = disj_map[d_ref]
        new_gdp.exactly1_constraints[new_d_ref] = new_lc_ref
    end

    for (lv_ref, bref) in old_gdp.indicator_to_binary
        if bref isa JuMP.VariableRef
            new_bref = var_map[bref]
        elseif bref isa JuMP.GenericAffExpr
            new_bref = _replace_variables_in_constraint(bref, var_map)
        end
        new_gdp.indicator_to_binary[lv_map[lv_ref]] = new_bref
    end

    for (lv_ref, con_refs) in old_gdp.indicator_to_constraints
        new_lvar_ref = lv_map[lv_ref]
        new_con_refs = Vector{Union{DisjunctConstraintRef{M}, DisjunctionRef{M}}}()
        for con_ref in con_refs
            new_con_ref = nothing
            if con_ref isa DisjunctConstraintRef
                new_con_ref = disj_con_map[con_ref]
            elseif con_ref isa DisjunctionRef
                new_con_ref = disj_map[con_ref]
            end
            push!(new_con_refs, new_con_ref)
        end
        new_gdp.indicator_to_constraints[new_lvar_ref] = new_con_refs
    end

    for (con_ref, lv_ref) in old_gdp.constraint_to_indicator
        if con_ref isa DisjunctConstraintRef
            new_gdp.constraint_to_indicator[disj_con_map[con_ref]] = lv_map[lv_ref]
        elseif con_ref isa DisjunctionRef
            new_gdp.constraint_to_indicator[disj_map[con_ref]] = lv_map[lv_ref]
        end
    end

    for (v, bounds) in old_gdp.variable_bounds
        new_gdp.variable_bounds[var_map[v]] = bounds
    end

    new_gdp.solution_method = old_gdp.solution_method
    new_gdp.ready_to_optimize = old_gdp.ready_to_optimize

    return lv_map
end