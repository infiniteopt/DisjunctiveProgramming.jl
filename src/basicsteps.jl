################################################################################
#                              INPUT CHECKING
################################################################################
# Verify a global constraint can be intersected into a disjunction
function _check_global_constraint(model::JuMP.AbstractModel, cref)
    if cref isa Union{DisjunctConstraintRef, DisjunctionRef,
        LogicalConstraintRef}
        error("Global `constraints` must be regular model constraints, " *
              "not `$(typeof(cref))`.")
    end
    JuMP.is_valid(model, cref) || error(
        "Global constraint `$cref` does not belong to the model.")
    cref in _reformulation_constraints(model) && error(
        "Global constraint `$cref` is a reformulation constraint and " *
        "cannot be intersected into a disjunction.")
    con = JuMP.constraint_object(cref)
    if con isa JuMP.ScalarConstraint &&
        JuMP.jump_function(con) isa JuMP.AbstractVariableRef
        error("Global constraint `$cref` constrains a single variable " *
              "(e.g., a variable bound or integrality constraint) and " *
              "cannot be intersected into a disjunction.")
    end
    supported = con isa JuMP.ScalarConstraint ||
        (con isa JuMP.VectorConstraint && JuMP.moi_set(con) isa
            Union{_MOI.Nonnegatives, _MOI.Nonpositives, _MOI.Zeros})
    supported || error("Global constraint `$cref` with set " *
        "`$(JuMP.moi_set(con))` cannot be intersected into a disjunction.")
    _check_expression(JuMP.jump_function(con))
    return
end

# Verify the basic step inputs before any model mutation
function _check_basic_step_input(
    model::JuMP.AbstractModel,
    disjunctions::Vector{<:DisjunctionRef},
    constraints::Vector
    )
    is_gdp_model(model) || error(
        "Basic steps can only be applied to `GDPModel`s.")
    isempty(disjunctions) && error(
        "Basic steps require at least one disjunction.")
    if length(disjunctions) == 1 && isempty(constraints)
        error("A basic step on a single disjunction requires global " *
              "`constraints` to intersect with it (improper basic step).")
    end
    allunique(disjunctions) || error(
        "The `disjunctions` for a basic step must be unique.")
    for dref in disjunctions
        JuMP.is_valid(model, dref) || error(
            "Disjunction `$dref` does not belong to the model.")
        disj = JuMP.constraint_object(dref)
        disj.nested && error(
            "Basic steps do not support nested disjunction `$dref`.")
        if !haskey(_exactly1_constraints(model), dref) &&
            !any(has_logical_complement.(disj.indicators))
            error("Basic steps require disjunctions where exactly one " *
                  "disjunct is selected, but `exactly1 = false` for " *
                  "disjunction `$dref`.")
        end
        for lvref in disj.indicators
            crefs = get(_indicator_to_constraints(model), lvref, [])
            if any(cref -> cref isa DisjunctionRef, crefs)
                error("Basic steps do not support disjuncts that contain " *
                      "nested disjunctions (indicator `$lvref`).")
            end
        end
    end
    all_indicators = [lv for d in disjunctions
                      for lv in JuMP.constraint_object(d).indicators]
    allunique(all_indicators) || error(
        "The `disjunctions` for a basic step share indicator variables.")
    indicator_set = Set(all_indicators)
    input_set = Set(disjunctions)
    for (idx, disj) in _disjunctions(model)
        dref = DisjunctionRef(model, idx)
        dref in input_set && continue
        if any(in(indicator_set), disj.constraint.indicators)
            error("An indicator of the `disjunctions` for a basic step " *
                  "is also used by disjunction `$dref`.")
        end
    end
    allunique(constraints) || error(
        "The global `constraints` for a basic step must be unique.")
    for cref in constraints
        _check_global_constraint(model, cref)
    end
    return
end

################################################################################
#                              PRODUCT CONSTRUCTION
################################################################################
# Snapshot constraint refs as (object, name) pairs
_snapshot(crefs) = [(JuMP.constraint_object(c), JuMP.name(c)) for c in crefs]

# Snapshot the constraint contents of each input disjunct before mutating
function _snapshot_disjunct_constraints(
    model::M,
    indicator_vectors::Vector{Vector{LogicalVariableRef{M}}}
    ) where {M <: JuMP.AbstractModel}
    snapshot = Dict{LogicalVariableRef{M},
        Vector{Tuple{JuMP.AbstractConstraint, String}}}()
    for lvref in Iterators.flatten(indicator_vectors)
        snapshot[lvref] =
            _snapshot(get(_indicator_to_constraints(model), lvref, []))
    end
    return snapshot
end

"""
    product_indicator_variable(model::JuMP.AbstractModel, parents)

Return the `LogicalVariable` to add as a product-disjunct indicator
formed from the `parents` indicator variables. Extend this for model
types whose indicators carry additional structure (e.g., an indicator
that varies over the parents' infinite parameters).
"""
function product_indicator_variable(model::JuMP.AbstractModel, parents)
    return LogicalVariable(nothing, nothing, nothing)
end

# Add the snapshotted global constraints to the disjunct of `lvref`
function _intersect_globals(model, lvref, global_snapshot)
    for (con, cname) in global_snapshot
        JuMP.add_constraint(model, _DisjunctConstraint(con, lvref), cname)
    end
    return
end

# Create the product disjuncts, one per element of the cartesian product
# of the input disjunctions' disjuncts, each populated with its parents'
# constraints and the intersected global constraints
function _add_product_disjuncts(
    model::M,
    indicator_vectors::Vector{Vector{LogicalVariableRef{M}}},
    disjunct_snapshot::Dict,
    global_snapshot::Vector,
    name::String,
    relax_products::Bool
    ) where {M <: JuMP.AbstractModel}
    dims = Tuple(length(inds) for inds in indicator_vectors)
    products = Array{LogicalVariableRef{M}}(undef, dims)
    for idx in CartesianIndices(products)
        parents = [inds[idx[axis]]
                   for (axis, inds) in enumerate(indicator_vectors)]
        w_name = isempty(name) ? "" :
            string(name, "[", join(Tuple(idx), ","), "]")
        w = JuMP.add_variable(
            model, product_indicator_variable(model, parents), w_name)
        products[idx] = w
        # constraint objects are shared across product disjuncts; safe
        # since reformulations never mutate stored functions
        for parent in parents, (con, cname) in disjunct_snapshot[parent]
            JuMP.add_constraint(model, _DisjunctConstraint(con, w), cname)
        end
        _intersect_globals(model, w, global_snapshot)
    end
    if relax_products
        # the binary originals force the relaxed product indicators
        # integral through the linking constraints
        for w in products
            bvref = binary_variable(w)
            JuMP.unset_binary(bvref)
            JuMP.set_lower_bound(bvref, 0)
            JuMP.set_upper_bound(bvref, 1)
        end
    end
    return products
end

# Add the linking constraints `Y in Exactly(w_slice)` which reformulate
# to the marginal equalities y = sum(w)
function _add_linking_constraints(
    model::M,
    products::Array{LogicalVariableRef{M}},
    indicator_vectors::Vector{Vector{LogicalVariableRef{M}}},
    name::String
    ) where {M <: JuMP.AbstractModel}
    for (axis, inds) in enumerate(indicator_vectors)
        for (i, lvref) in enumerate(inds)
            slice = vec(collect(selectdim(products, axis, i)))
            link_name = isempty(name) ? "" :
                string(name, "_link[", axis, ",", i, "]")
            con = JuMP.build_constraint(error, slice, Exactly(lvref))
            JuMP.add_constraint(model, con, link_name)
        end
    end
    return
end

################################################################################
#                              INPUT REMOVAL
################################################################################
# Remove the original disjunctions, their disjunct constraints, and the
# intersected global constraints (their content now lives in the product
# disjunction, so the original logical variables are kept)
function _delete_basic_step_inputs(
    model::JuMP.AbstractModel,
    disjunctions::Vector{<:DisjunctionRef},
    constraints::Vector
    )
    for dref in disjunctions
        for lvref in JuMP.constraint_object(dref).indicators
            # copy since delete mutates the mapped vector
            crefs = copy(get(_indicator_to_constraints(model), lvref, []))
            for cref in crefs
                JuMP.delete(model, cref)
            end
        end
        JuMP.delete(model, dref)
    end
    for cref in constraints
        JuMP.delete(model, cref)
    end
    return
end

################################################################################
#                              BASIC STEP API
################################################################################
"""
    apply_basic_step(
        model::JuMP.AbstractModel,
        disjunctions::Vector{<:DisjunctionRef};
        [constraints::Vector = JuMP.ConstraintRef[]],
        [name::String = ""],
        [relax_products::Bool = false]
        )::DisjunctionRef

Apply a basic step to `disjunctions`, replacing them with the
equivalent product disjunction whose disjuncts are the intersections
of the original disjuncts. The feasible region is unchanged, but the
hull relaxation is at least as tight as before. The original
disjunctions and their disjunct constraints are deleted; the original
logical variables are kept and linked to the product indicators.
With a single disjunction, the `constraints` are intersected into it
in place.

Each input disjunction must use `exactly1 = true` (or a
logical-complement pair) and must not be nested or contain nested
disjunctions. The number of product disjuncts is the product of the
input disjunction sizes, so repeated basic steps grow the model
multiplicatively (a warning is emitted above 100).

## Keyword Arguments
- `constraints::Vector`: Global constraints to intersect into every
  product disjunct; deleted from the model afterwards.
- `name::String`: Base name for the product disjunction, its
  indicators (`name[i,j]`), and the linking constraints
  (`name_link[k,i]`). Anonymous by default.
- `relax_products::Bool`: Relax the product indicator binaries to
  `[0, 1]` (valid since the linking constraints force them integral).

## Returns
- `DisjunctionRef`: The product disjunction (or `first(disjunctions)`
  when a single disjunction is given).
"""
function apply_basic_step(
    model::M,
    disjunctions::Vector{DisjunctionRef{M}};
    constraints::Vector = JuMP.ConstraintRef[],
    name::String = "",
    relax_products::Bool = false
    ) where {M <: JuMP.AbstractModel}
    _check_basic_step_input(model, disjunctions, constraints)
    global_snapshot = _snapshot(constraints)
    if length(disjunctions) == 1
        dref = only(disjunctions)
        for lvref in JuMP.constraint_object(dref).indicators
            _intersect_globals(model, lvref, global_snapshot)
        end
        _delete_basic_step_inputs(model, empty(disjunctions), constraints)
        _set_ready_to_optimize(model, false)
        return dref
    end
    indicator_vectors = [JuMP.constraint_object(dref).indicators
                         for dref in disjunctions]
    num_products = prod(length(inds) for inds in indicator_vectors)
    num_products > 100 && @warn "This basic step creates $num_products " *
        "product disjuncts; repeated basic steps grow the model " *
        "multiplicatively."
    disjunct_snapshot = _snapshot_disjunct_constraints(model, indicator_vectors)
    products = _add_product_disjuncts(model, indicator_vectors,
        disjunct_snapshot, global_snapshot, name, relax_products)
    new_dref = disjunction(model, vec(products), name)
    _add_linking_constraints(model, products, indicator_vectors, name)
    _delete_basic_step_inputs(model, disjunctions, constraints)
    _set_ready_to_optimize(model, false)
    return new_dref
end
