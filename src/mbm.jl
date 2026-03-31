################################################################################
#                              HELPER FUNCTIONS
################################################################################
# Check if M result contains only zeros.
_is_all_zeros(M::Number) = iszero(M)
_is_all_zeros(M::AbstractVector) = all(iszero, M)
_is_all_zeros(::Any) = false

################################################################################
#               CONSTRAINT, DISJUNCTION, DISJUNCT REFORMULATION
################################################################################
#Reformulates the disjunction using multiple big-M values
function reformulate_disjunction(
    model::JuMP.AbstractModel,
    disj::Disjunction,
    method::MBM
    )
    mbm = _MBM(method, model)
    disjunct_cons = Dict{LogicalVariableRef, Vector{JuMP.AbstractConstraint}}()
    for d in disj.indicators
        d in mbm.deactivated && continue
        mbm.subproblem_indicators = filter(
            x -> x != d && !(x in mbm.deactivated), disj.indicators)
        disjunct_cons[d] = Vector{JuMP.AbstractConstraint}()
        _reformulate_disjunct(model, disjunct_cons[d], d, mbm)
    end
    # Collect constraints from non-deactivated disjuncts. It needs to be
    # in a separate loop because disjuncts are only deactivated by looking
    # at reforming other disjuncts (subproblem infeasibility).
    ref_cons = Vector{JuMP.AbstractConstraint}()
    for d in disj.indicators
        d in mbm.deactivated && continue
        haskey(disjunct_cons, d) && append!(ref_cons, disjunct_cons[d])
    end
    return ref_cons
end

# Reformulates a disjunct represented by lvref using per-constraint M values.
# Gets its own set of M_{ie,i'} values for each other disjunct term i'.
function _reformulate_disjunct(
    model::JuMP.AbstractModel,
    ref_cons::Vector{JuMP.AbstractConstraint},
    lvref::LogicalVariableRef, 
    method::_MBM
    )
    !haskey(_indicator_to_constraints(model), lvref) && return
    # Filter out deactivated disjuncts from binary variable mapping in
    # the event we've identified some infeasible disjuncts already
    active_subproblem_indicators = filter(d -> !(d in method.deactivated), method.subproblem_indicators)
    bconref = Dict(d => binary_variable(d) for d in active_subproblem_indicators)

    constraints = _indicator_to_constraints(model)[lvref]
    filtered_constraints = [
        c for c in constraints if c isa DisjunctConstraintRef]

    # For each constraint, compute its own set of M values
    for cref in filtered_constraints
        empty!(method.M)

        for d in method.subproblem_indicators
            # Skip already-deactivated disjuncts
            d in method.deactivated && continue

            d_constraints = _indicator_to_constraints(model)[d]
            disjunct_constraints = [
                c for c in d_constraints if c isa DisjunctConstraintRef]
            if !isempty(disjunct_constraints)
                M_result = _maximize_M(model, JuMP.constraint_object(cref),
                    disjunct_constraints, method)
                # Check for infeasibility: disjunct d
                # has empty feasible region
                if M_result === nothing
                    push!(method.deactivated, d)
                    @warn "Disjunct $(d) is infeasible, deactivating."
                    delete!(bconref, d)
                else
                    method.M[d] = M_result
                end
            end
        end

        con = JuMP.constraint_object(cref)
        # Check if all M values are zero for that constraint. If so, it
        # should be enforced globally (no reformulation with binaries).
        if !isempty(method.M) && all(
               _is_all_zeros(method.M[d]) for d in keys(method.M))
            push!(ref_cons, con)
        else
            append!(ref_cons,
                reformulate_disjunct_constraint(model, con, bconref, method))
        end
    end
    return ref_cons
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel, 
    con::Disjunction,
    bconref::Union{
        Dict{<:LogicalVariableRef, <:JuMP.AbstractVariableRef},
        Dict{<:LogicalVariableRef, <:JuMP.GenericAffExpr}
        },
    method::_MBM
    )
    ref_cons = reformulate_disjunction(model, con, MBM(method.optimizer))
    new_ref_cons = Vector{JuMP.AbstractConstraint}()
    for ref_con in ref_cons
        append!(new_ref_cons,
            reformulate_disjunct_constraint(model, ref_con, bconref, method))
    end
    return new_ref_cons
end

# Uses per-row M values: method.M[d][row] for each disjunct d
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bconref::Union{
        Dict{<:LogicalVariableRef, <:JuMP.AbstractVariableRef},
        Dict{<:LogicalVariableRef, <:JuMP.GenericAffExpr}
        },
    method::_MBM
    ) where {T, S <: _MOI.Nonpositives, R}
    new_func = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] - sum(method.M[d][i] * bconref[d] for d in keys(method.M)))
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

# Uses per-row M values: method.M[d][row] for each disjunct d
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bconref::Union{
        Dict{<:LogicalVariableRef, <:JuMP.AbstractVariableRef},
        Dict{<:LogicalVariableRef, <:JuMP.GenericAffExpr}
        },
    method::_MBM
    ) where {T, S <: _MOI.Nonnegatives, R}
    new_func = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] + sum(method.M[d][i] * bconref[d] for d in keys(method.M)))
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

# Uses per-row M values: method.M[d][row] for each disjunct d
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.VectorConstraint{T, S, R},
    bconref::Union{
        Dict{<:LogicalVariableRef, <:JuMP.AbstractVariableRef},
        Dict{<:LogicalVariableRef, <:JuMP.GenericAffExpr}
        },
    method::_MBM
    ) where {T, S <: _MOI.Zeros, R}
    upper_expr = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] + sum(method.M[d][i] * bconref[d] for d in keys(method.M)))
    lower_expr = JuMP.@expression(model, [i=1:con.set.dimension],
        con.func[i] - sum(method.M[d][i] * bconref[d] for d in keys(method.M)))
    upper_con = JuMP.build_constraint(
        error, upper_expr, MOI.Nonnegatives(con.set.dimension))
    lower_con = JuMP.build_constraint(
        error, lower_expr, MOI.Nonpositives(con.set.dimension))
    return [upper_con, lower_con]
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bconref::Union{
        Dict{<:LogicalVariableRef, <:JuMP.AbstractVariableRef},
        Dict{<:LogicalVariableRef, <:JuMP.GenericAffExpr}
        },
    method::_MBM
    ) where {T, S <: _MOI.LessThan}
    new_func = JuMP.@expression(model, con.func - sum(
        method.M[i] * bconref[i] for i in keys(method.M)))
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bconref::Union{
        Dict{<:LogicalVariableRef, <:JuMP.AbstractVariableRef},
        Dict{<:LogicalVariableRef, <:JuMP.GenericAffExpr}
        },
    method::_MBM
    ) where {T, S <: _MOI.GreaterThan}
    new_func = JuMP.@expression(model, con.func + sum(
        method.M[i] * bconref[i] for i in keys(method.M)))
    reform_con = JuMP.build_constraint(error, new_func, con.set)
    return [reform_con]
end

# Uses per-bound M values: method.M[d][1] for lower, method.M[d][2] for upper
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bconref::Union{
        Dict{<:LogicalVariableRef, <:JuMP.AbstractVariableRef},
        Dict{<:LogicalVariableRef, <:JuMP.GenericAffExpr}
        },
    method::_MBM
    ) where {T, S <: _MOI.EqualTo}
    # M[d][1] = M for GreaterThan (lower), M[d][2] = M for LessThan (upper)
    lower_func = JuMP.@expression(model, con.func + sum(
        method.M[d][1] * bconref[d] for d in keys(method.M)))
    upper_func = JuMP.@expression(model, con.func - sum(
        method.M[d][2] * bconref[d] for d in keys(method.M)))
    lower_con = JuMP.build_constraint(
        error, lower_func, MOI.GreaterThan(con.set.value))
    upper_con = JuMP.build_constraint(
        error, upper_func, MOI.LessThan(con.set.value))
    return [lower_con, upper_con]
end

# Uses per-bound M values: method.M[d][1] for lower, method.M[d][2] for upper
function reformulate_disjunct_constraint(
    model::JuMP.AbstractModel,
    con::JuMP.ScalarConstraint{T, S},
    bconref::Union{
        Dict{<:LogicalVariableRef, <:JuMP.AbstractVariableRef},
        Dict{<:LogicalVariableRef, <:JuMP.GenericAffExpr}
        },
    method::_MBM
    ) where {T, S <: _MOI.Interval}
    set_values = _set_values(con.set)
    # M[d][1] = M for GreaterThan (lower), M[d][2] = M for LessThan (upper)
    lower_func = JuMP.@expression(model, con.func + sum(
        method.M[d][1] * bconref[d] for d in keys(method.M)))
    upper_func = JuMP.@expression(model, con.func - sum(
        method.M[d][2] * bconref[d] for d in keys(method.M)))
    lower_con = JuMP.build_constraint(
        error, lower_func, MOI.GreaterThan(set_values[1]))
    upper_con = JuMP.build_constraint(
        error, upper_func, MOI.LessThan(set_values[2]))
    return [lower_con, upper_con]
end

function reformulate_disjunct_constraint(::JuMP.AbstractModel,
    ::F,
    ::Union{Dict{<:LogicalVariableRef, <:JuMP.AbstractVariableRef},
        Dict{<:LogicalVariableRef, <:JuMP.GenericAffExpr}},
    ::_MBM
    ) where {F}
    error("Constraint type $(typeof(F)) is not supported by " *
          "the Multiple Big-M reformulation method.")
end

################################################################################
#                     MULTIPLE BIG-M REFORMULATION
################################################################################

"""
    prepare_objectives(model, obj::ScalarConstraint, sub::GDPSubmodel)

Convert a constraint into objective expressions for M-value maximization.
Returns a vector of JuMP expressions to pass to `_raw_M`. The base method
produces a single-element vector by mapping variables through `sub.fwd`.
"""
function prepare_objectives(
    ::JuMP.AbstractModel,
    obj::JuMP.ScalarConstraint{T, S},
    sub::GDPSubmodel
    ) where {T, S <: _MOI.LessThan}
    flat_map = Dict(v => ws[1] for (v, ws) in sub.fwd)
    expr = -obj.set.upper +_replace_variables_in_constraint(obj.func, flat_map)
    return [expr]
end

function prepare_objectives(
    ::JuMP.AbstractModel,
    obj::JuMP.ScalarConstraint{T, S},
    sub::GDPSubmodel
    ) where {T, S <: _MOI.GreaterThan}
    flat_map = Dict(v => ws[1] for (v, ws) in sub.fwd)
    expr = obj.set.lower -_replace_variables_in_constraint(obj.func, flat_map)
    return [expr]
end

# Solve the submodel for each objective and return raw M values as a vector, or
# nothing if infeasible. Order of results matches order of objectives.
function _raw_M(
    sub::GDPSubmodel,
    objectives::Vector{<:JuMP.AbstractJuMPScalar},
    method::_MBM
    )
    M_vals = typeof(method.default_M)[]
    for obj_expr in objectives
        JuMP.@objective(sub.model, Max, obj_expr)
        # Clear start values before each solve to prevent NaN
        # residue from a previous non-feasible solve
        for v in JuMP.all_variables(sub.model)
            JuMP.set_start_value(v, nothing)
        end
        JuMP.optimize!(sub.model)
        if JuMP.termination_status(sub.model) == _MOI.INFEASIBLE
            return nothing
        elseif !JuMP.is_solved_and_feasible(sub.model)
            push!(M_vals, method.default_M)
        else
            push!(M_vals, max(
                JuMP.objective_value(sub.model),
                zero(method.default_M))
                )
        end
    end
    return M_vals
end

"""
    aggregate_M_values(model, vals::AbstractVector)

Reduce a vector of raw M values from `_raw_M` to the final form used
during constraint reformulation. The base method returns the single
element from a length-1 vector. Extensions (e.g., InfiniteOpt) override
to aggregate across multiple support points (e.g., interpolating K
per-support M values into a parameter function).
"""
function aggregate_M_values(
    ::JuMP.AbstractModel,
    vals::AbstractVector
    )
    return only(vals)
end

# Dispatch over constraint types to compute M values. Scalar
# LE/GE: prepare objectives, solve, finalize.
function _maximize_M(
    model::JuMP.AbstractModel,
    objective::JuMP.ScalarConstraint{T, S},
    constraints::Vector{<:DisjunctConstraintRef},
    method::_MBM
    ) where {T, S <: Union{_MOI.LessThan, _MOI.GreaterThan}}
    sub = _get_submodel(model, constraints, method)
    objectives = prepare_objectives(model, objective, sub)
    raw = _raw_M(sub, objectives, method)
    raw === nothing && return nothing
    return aggregate_M_values(model, raw)
end

# Helper: get or create the submodel for a set of constraints.
function _get_submodel(
    model::JuMP.AbstractModel,
    constraints::Vector{<:DisjunctConstraintRef},
    method::_MBM
    )
    indicator = _constraint_to_indicator(
        model)[first(constraints)]
    if !haskey(method.model_cache, indicator)
        method.model_cache[indicator] = create_submodel(
            model, constraints, method)
    end
    return method.model_cache[indicator]
end

# EqualTo: solve both GreaterThan and LessThan directions, finalize each.
function _maximize_M(
    model::JuMP.AbstractModel,
    objective::JuMP.ScalarConstraint{T, S},
    constraints::Vector{<:DisjunctConstraintRef},
    method::_MBM
    ) where {T, S <: _MOI.EqualTo}
    sub = _get_submodel(model, constraints, method)
    set_value = objective.set.value
    ge_obj = JuMP.ScalarConstraint(objective.func, MOI.GreaterThan(set_value))
    le_obj = JuMP.ScalarConstraint(objective.func, MOI.LessThan(set_value))
    raw_lower = _raw_M(sub,prepare_objectives(model, ge_obj, sub),method)
    raw_upper = _raw_M(sub,prepare_objectives(model, le_obj, sub),method)
    (raw_lower === nothing || raw_upper === nothing) &&
        return nothing
    return [aggregate_M_values(model, raw_lower),aggregate_M_values(model, raw_upper)]
end

# Interval: solve both lower and upper bound directions, finalize each.
function _maximize_M(
    model::JuMP.AbstractModel,
    objective::JuMP.ScalarConstraint{T, S},
    constraints::Vector{<:DisjunctConstraintRef},
    method::_MBM
    ) where {T, S <: _MOI.Interval}
    sub = _get_submodel(model, constraints, method)
    set_values = _set_values(objective.set)
    ge_obj = JuMP.ScalarConstraint(objective.func,
        MOI.GreaterThan(set_values[1]))
    le_obj = JuMP.ScalarConstraint(objective.func,
        MOI.LessThan(set_values[2]))
    raw_lower = _raw_M(sub,prepare_objectives(model, ge_obj, sub),method)
    raw_upper = _raw_M(sub,prepare_objectives(model, le_obj, sub),method)
    (raw_lower === nothing || raw_upper === nothing) &&
        return nothing
    return [aggregate_M_values(model, raw_lower),aggregate_M_values(model, raw_upper)]
end

# Nonpositives: per-row LessThan solves for each dimension of the vector.
function _maximize_M(
    model::JuMP.AbstractModel,
    objective::JuMP.VectorConstraint{T, S, R},
    constraints::Vector{<:DisjunctConstraintRef},
    method::_MBM
    ) where {T, S <: _MOI.Nonpositives, R}
    sub = _get_submodel(model, constraints, method)
    val_type = JuMP.value_type(typeof(model))
    results = Any[]
    for i in 1:objective.set.dimension
        le_obj = JuMP.ScalarConstraint(
            objective.func[i], MOI.LessThan(zero(val_type)))
        raw = _raw_M(sub,prepare_objectives(model, le_obj, sub),method)
        raw === nothing && return nothing
        push!(results, aggregate_M_values(model, raw))
    end
    return results
end

# Nonnegatives: per-row GreaterThan solves for each dimension of the vector.
function _maximize_M(
    model::JuMP.AbstractModel,
    objective::JuMP.VectorConstraint{T, S, R},
    constraints::Vector{<:DisjunctConstraintRef},
    method::_MBM
    ) where {T, S <: _MOI.Nonnegatives, R}
    sub = _get_submodel(model, constraints, method)
    val_type = JuMP.value_type(typeof(model))
    results = Any[]
    for i in 1:objective.set.dimension
        ge_obj = JuMP.ScalarConstraint(
            objective.func[i], MOI.GreaterThan(zero(val_type)))
        raw = _raw_M(sub,prepare_objectives(model, ge_obj, sub),method)
        raw === nothing && return nothing
        push!(results, aggregate_M_values(model, raw))
    end
    return results
end

# Zeros: per-row element-wise max of GE and LE raw values, then finalize.
function _maximize_M(
    model::JuMP.AbstractModel,
    objective::JuMP.VectorConstraint{T, S, R},
    constraints::Vector{<:DisjunctConstraintRef},
    method::_MBM
    ) where {T, S <: _MOI.Zeros, R}
    sub = _get_submodel(model, constraints, method)
    val_type = JuMP.value_type(typeof(model))
    results = Any[]
    for i in 1:objective.set.dimension
        ge_obj = JuMP.ScalarConstraint(
            objective.func[i], MOI.GreaterThan(zero(val_type)))
        le_obj = JuMP.ScalarConstraint(
            objective.func[i], MOI.LessThan(zero(val_type)))
        raw_ge = _raw_M(sub,prepare_objectives(model, ge_obj, sub),method)
        raw_le = _raw_M(sub,prepare_objectives(model, le_obj, sub),method)
        (raw_ge === nothing || raw_le === nothing) &&
            return nothing
        push!(results, aggregate_M_values(model, max.(raw_ge, raw_le)))
    end
    return results
end

function _maximize_M(
    ::JuMP.AbstractModel, ::F,
    ::Vector{<:DisjunctConstraintRef}, ::_MBM
    ) where {F}
    error("This type of constraints and objective constraint " *
          "has not been implemented for MBM subproblems\nF: $(F)")
end

"""
    create_submodel(model, constraints, method::_MBM)

Build a `GDPSubmodel` representing a disjunct's feasible region for
MBM subproblem solves. Copies the model's decision variables and adds
the given disjunct constraints. Submodels are cached in `method.model_cache`
by indicator.
"""
function create_submodel(
    model::JuMP.AbstractModel,
    constraints::Vector{<:DisjunctConstraintRef},
    method::_MBM
    )
    var_type = JuMP.variable_ref_type(model)
    sub_model = _copy_model(model)
    dec_vars = collect_all_vars(model)
    fwd = Dict{var_type, Vector{var_type}}()

    for var in dec_vars
        copy_var = variable_copy(sub_model, var)
        fwd[var] = [copy_var]
    end

    for cref in constraints
        con = JuMP.constraint_object(cref)
        flat_map = Dict(v => ws[1] for (v, ws) in fwd)
        expr = _replace_variables_in_constraint(
            con.func, flat_map)
        T = one(JuMP.value_type(typeof(sub_model)))
        JuMP.@constraint(sub_model, expr * T in con.set)
    end

    JuMP.set_optimizer(sub_model, method.optimizer)
    JuMP.set_silent(sub_model)

    return GDPSubmodel(sub_model, dec_vars, fwd)
end

################################################################################
#                    REPLACE VARIABLES IN CONSTRAINT
################################################################################

# Replace variable refs in an expression using a map. Uses AbstractDict
# because the InfiniteModel MBM path maps decision vars to VariableRefs
# and parameter functions to Numbers in the same dict (via _build_flat_map).
function _replace_variables_in_constraint(
    fun::JuMP.AbstractVariableRef,
    var_map::AbstractDict
    )
    return var_map[fun]
end

# Infer the variable reference type from the map values, falling back to the
# expression's own type.
function _var_ref_type(
    ::Type{JuMP.GenericAffExpr{C, V}},
    var_map::AbstractDict
    ) where {C, V}
    for val in values(var_map)
        if val isa JuMP.AbstractVariableRef
            return typeof(val)
        end
    end
    return V
end

function _replace_variables_in_constraint(
    fun::T, var_map::AbstractDict
    ) where {T <: JuMP.GenericAffExpr}
    C = JuMP.value_type(T)
    W = _var_ref_type(T, var_map)
    new_aff = zero(JuMP.GenericAffExpr{C, W})
    for (var, coef) in fun.terms
        JuMP.add_to_expression!(new_aff, coef, var_map[var])
    end
    new_aff.constant = new_aff.constant + fun.constant
    return new_aff
end

function _replace_variables_in_constraint(
    fun::T, var_map::AbstractDict
    ) where {T <: JuMP.GenericQuadExpr}
    C = JuMP.value_type(T)
    W = _var_ref_type(typeof(fun.aff), var_map)
    new_quad = zero(JuMP.GenericQuadExpr{C, W})
    for (vars, coef) in fun.terms
        JuMP.add_to_expression!(new_quad,
            coef * var_map[vars.a] * var_map[vars.b])
    end
    new_aff = _replace_variables_in_constraint(fun.aff, var_map)
    JuMP.add_to_expression!(new_quad, new_aff)
    return new_quad
end

function _replace_variables_in_constraint(fun::Number, var_map::AbstractDict)
    return fun
end

function _replace_variables_in_constraint(fun::T,
    var_map::AbstractDict) where {T <: JuMP.GenericNonlinearExpr}
    new_args = Any[_replace_variables_in_constraint(
        arg, var_map) for arg in fun.args]
    return T(fun.head, new_args)
end

function _replace_variables_in_constraint(fun::Vector, var_map::AbstractDict)
    return [_replace_variables_in_constraint(expr,
        var_map) for expr in fun]
end
