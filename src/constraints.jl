################################################################################
#                         HELPER SET MAPPING FUNCTIONS
################################################################################
# helper functions to get the value of an MOI set
_set_value(set::_MOI.LessThan) = set.upper
_set_value(set::_MOI.GreaterThan) = set.lower
_set_value(set::_MOI.EqualTo) = set.value
_set_values(set::_MOI.EqualTo) = (set.value, set.value)
_set_values(set::_MOI.Interval) = (set.lower, set.upper)

# helper functions to reformulate vector constraints to indicator constraints
_vec_to_scalar_set(::_MOI.Nonpositives) = _MOI.LessThan(0)
_vec_to_scalar_set(::_MOI.Nonnegatives) = _MOI.GreaterThan(0)
_vec_to_scalar_set(::_MOI.Zeros) = _MOI.EqualTo(0)

# helper functions to map jump selector to moi selector sets
_jump_to_moi_selector(::Exactly) = _MOIExactly
_jump_to_moi_selector(::AtLeast) = _MOIAtLeast
_jump_to_moi_selector(::AtMost) = _MOIAtMost

# helper functions to map selectors to scalar sets
_vec_to_scalar_set(::_MOIExactly) = _MOI.EqualTo
_vec_to_scalar_set(::_MOIAtLeast) = _MOI.GreaterThan
_vec_to_scalar_set(::_MOIAtMost) = _MOI.LessThan

################################################################################
#                         BOILERPLATE EXTENSION METHODS
################################################################################
for (RefType, loc) in ((:DisjunctConstraintRef, :disjunct_constraints),
                       (:DisjunctionRef, :disjunctions),
                       (:LogicalConstraintRef, :logical_constraints))
    @eval begin
        @doc """
            JuMP.owner_model(cref::$($RefType))

        Return the model to which `cref` belongs.
        """
        JuMP.owner_model(cref::$RefType) = cref.model

        @doc """
            JuMP.index(cref::$($RefType))

        Return the index constraint associated with `cref`.
        """
        JuMP.index(cref::$RefType) = cref.index

        @doc """
            JuMP.is_valid(model::JuMP.AbstractModel, cref::$($RefType))

        Return `true` if `cref` refers to a valid constraint in the `GDP model`.
        """
        function JuMP.is_valid(model::JuMP.AbstractModel, cref::$RefType)
            return model === JuMP.owner_model(cref) && haskey(gdp_data(model).$loc, JuMP.index(cref))
        end

        # Get the ConstraintData object
        function _constraint_data(cref::$RefType)
            return gdp_data(JuMP.owner_model(cref)).$loc[JuMP.index(cref)]
        end

        @doc """
            JuMP.name(cref::$($RefType))

        Get a constraint's name attribute.
        """
        function JuMP.name(cref::$RefType)
            return _constraint_data(cref).name
        end

        @doc """
            JuMP.set_name(cref::$($RefType), name::String)

        Set a constraint's name attribute.
        """
        function JuMP.set_name(cref::$RefType, name::String)
            _constraint_data(cref).name = name
            _set_ready_to_optimize(JuMP.owner_model(cref), false)
            return
        end

        @doc """
            JuMP.constraint_object(cref::$($RefType))

        Return the underlying constraint data for the constraint
            referenced by `cref`.
        """
        function JuMP.constraint_object(cref::$RefType)
            return _constraint_data(cref).constraint
        end

        # Extend Base methods
        function Base.:(==)(cref1::$RefType, cref2::$RefType)
            return cref1.model === cref2.model && cref1.index == cref2.index
        end
        Base.copy(cref::$RefType) = cref
        # @doc """
        #     Base.getindex(map::GenericReferenceMap, cref::$($RefType))

        # ...
        # """
        # function Base.getindex(map::ReferenceMap, cref::$RefType)
        #     $RefType(map.model, index(cref))
        # end
    end
end

"""
    JuMP.delete(model::JuMP.AbstractModel, cref::DisjunctionRef)

Delete a disjunction constraint from the `GDP model`.
"""
function JuMP.delete(model::JuMP.AbstractModel, cref::DisjunctionRef)
    @assert JuMP.is_valid(model, cref) "Disjunction does not belong to model."
    if JuMP.constraint_object(cref).nested
        lvref = gdp_data(model).constraint_to_indicator[cref]
        filter!(Base.Fix2(!=, cref), _indicator_to_constraints(model)[lvref])
        delete!(gdp_data(model).constraint_to_indicator, cref)
    end
    delete!(_disjunctions(model), JuMP.index(cref))
    exactly1_dict = gdp_data(model).exactly1_constraints
    if haskey(exactly1_dict, cref)
        JuMP.delete(model, exactly1_dict[cref])
        delete!(exactly1_dict, cref)
    end
    _set_ready_to_optimize(model, false)
    return
end

"""
    JuMP.delete(model::JuMP.AbstractModel, cref::DisjunctConstraintRef)

Delete a disjunct constraint from the `GDP model`.
"""
function JuMP.delete(model::JuMP.AbstractModel, cref::DisjunctConstraintRef)
    @assert JuMP.is_valid(model, cref) "Disjunctive constraint does not belong to model."
    delete!(_disjunct_constraints(model), JuMP.index(cref))
    lvref = gdp_data(model).constraint_to_indicator[cref]
    filter!(Base.Fix2(!=, cref), _indicator_to_constraints(model)[lvref])
    delete!(gdp_data(model).constraint_to_indicator, cref)
    _set_ready_to_optimize(model, false)
    return
end

"""
    JuMP.delete(model::JuMP.AbstractModel, cref::LogicalConstraintRef)

Delete a logical constraint from the `GDP model`.
"""
function JuMP.delete(model::JuMP.AbstractModel, cref::LogicalConstraintRef)
    @assert JuMP.is_valid(model, cref) "Logical constraint does not belong to model."
    delete!(_logical_constraints(model), JuMP.index(cref))
    _set_ready_to_optimize(model, false)
    return
end

################################################################################
#                              Disjunct Constraints
################################################################################
function _check_expression(expr::Ex) where {Ex <: JuMP.AbstractJuMPScalar}
    vars = Set{JuMP.variable_ref_type(expr)}()
    _interrogate_variables(v -> push!(vars, v), expr)
    if any(JuMP.is_binary.(vars))
        error(
            "Disjunct constraints can only contain continuous or integer variables, " *
            "not binary variables. If you are modeling binary decisions, " *
            "you should express these using the Logical variables that serve as indicators " *
            "to each of the disjuncts. If these are lower-level decisions to the disjunct " *
            "being defined, these can be modeled using nested disjunctions."
        )
    end
    return
end
function _check_expression(expr::AbstractVector)
    for ex in expr
        _check_expression(ex)
    end
    return
end

# Extend JuMP.model_convert for _DisjunctConstraint
function JuMP.model_convert(model::JuMP.AbstractModel, con::_DisjunctConstraint)
    return _DisjunctConstraint(JuMP.model_convert(model, con.constr), con.lvref)
end

"""
    JuMP.build_constraint(
        _error::Function,
        func,
        set::_MOI.AbstractScalarSet,
        tag::Disjunct
    )::_DisjunctConstraint

Extend `JuMP.build_constraint` to add constraints to disjuncts. This in
combination with `JuMP.add_constraint` enables the use of
`@constraint(model, [name], constr_expr, tag)`, where tag is a
`Disjunct(::Type{LogicalVariableRef})`. The user must specify the
`LogicalVariable` to use as the indicator for the `_DisjunctConstraint` being created.
"""
function JuMP.build_constraint(
    _error::Function,
    func,
    set::_MOI.AbstractScalarSet,
    tag::Disjunct
)
    _check_expression(func)
    constr = JuMP.build_constraint(_error, func, set)
    return _DisjunctConstraint(constr, tag.indicator)
end

# Allows for building DisjunctConstraints for VectorConstraints since these get parsed differently by JuMP (JuMP changes the set to a MOI.AbstractScalarSet)
for SetType in (
    JuMP.Nonnegatives, JuMP.Nonpositives, JuMP.Zeros,
    _MOI.Nonnegatives, _MOI.Nonpositives, _MOI.Zeros
)
    @eval begin
        @doc """
            JuMP.build_constraint(
                _error::Function,
                func,
                set::$($SetType),
                tag::Disjunct
            )::_DisjunctConstraint

        Extend `JuMP.build_constraint` to add `VectorConstraint`s to disjuncts.
        """
        function JuMP.build_constraint(
            _error::Function,
            func,
            set::$SetType,
            tag::Disjunct
        )
            _check_expression(func)
            constr = JuMP.build_constraint(_error, func, set)
            return _DisjunctConstraint(constr, tag.indicator)
        end
    end
end

# Allow intervals to handle tags
function JuMP.build_constraint(
    _error::Function,
    func::JuMP.AbstractJuMPScalar,
    lb::Real,
    ub::Real,
    tag::Disjunct
)
    _check_expression(func)
    constr = JuMP.build_constraint(_error, func, lb, ub)
    func = jump_function(constr)
    set = moi_set(constr)
    return JuMP.build_constraint(_error, func, set, tag)
end

"""
    JuMP.add_constraint(
        model::JuMP.AbstractModel,
        con::_DisjunctConstraint,
        name::String = ""
    )::DisjunctConstraintRef

Extend `JuMP.add_constraint` to add a [`Disjunct`](@ref) to a [`GDPModel`](@ref).
The constraint is added to the `GDPData` in the `.ext` dictionary of the `GDPModel`.
"""
function JuMP.add_constraint(
    model::JuMP.AbstractModel,
    con::_DisjunctConstraint,
    name::String = ""
)
    is_gdp_model(model) || error("Can only add disjunct constraints to `GDPModel`s.")
    data = ConstraintData(con.constr, name)
    idx = _MOIUC.add_item(gdp_data(model).disjunct_constraints, data)
    _add_indicator_var(con, DisjunctConstraintRef(model, idx), model)
    return DisjunctConstraintRef(model, idx)
end

################################################################################
#                              DISJUNCTIONS
################################################################################
# Add the variable mappings
function _add_indicator_var(
    con::_DisjunctConstraint{C, <:LogicalVariableRef},
    cref,
    model
    ) where {C <: AbstractConstraint}
    JuMP.is_valid(model, con.lvref) || error("Logical variable belongs to a different model.")
    if !haskey(_indicator_to_constraints(model), con.lvref)
        _indicator_to_constraints(model)[con.lvref] = Vector{Union{DisjunctConstraintRef, DisjunctionRef}}()
    end
    push!(_indicator_to_constraints(model)[con.lvref], cref)
    gdp_data(model).constraint_to_indicator[cref] = con.lvref
    return
end
# check disjunction
function _check_disjunction(
    _error,
    lvrefs::AbstractVector{<:LogicalVariableRef},
    model::M
    ) where {M <: JuMP.AbstractModel}
    isequal(unique(lvrefs), lvrefs) || _error("Not all the logical indicator variables are unique.")
    for lvref in lvrefs
        if !JuMP.is_valid(model, lvref)
            _error("`$lvref` is not a valid logical variable reference.")
        end
    end
    if length(lvrefs) != 2 && any(has_logical_complement.(lvrefs))
        _error("Can only use logical complement variables in Disjunctions " *
               "with two disjuncts.")
    elseif length(lvrefs) == 2 && any(has_logical_complement.(lvrefs))
        T = JuMP.value_type(M)
        V = JuMP.variable_ref_type(M)
        expr1 = convert(JuMP.GenericAffExpr{T, V}, binary_variable(first(lvrefs)))
        expr2 = 1 - binary_variable(last(lvrefs))
        if !JuMP.isequal_canonical(expr1, expr2)
            _error("When using logical complement variables in a disjunction, " *
                   "both logical variables must be the complement of one another.")
        end
    end
    return lvrefs
end

# Write the main function for creating disjunctions that is macro friendly
function _create_disjunction(
    _error::Function,
    model::JuMP.AbstractModel,
    structure::Vector{<:LogicalVariableRef},
    name::String,
    nested::Bool
    )
    is_gdp_model(model) || error("Can only add disjunctions to `GDPModel`s.")

    # build the disjunction
    indicators = _check_disjunction(_error, structure, model)
    disjunction = Disjunction(indicators, nested)

    # add it to the model
    disjunction_data = ConstraintData(disjunction, name)
    idx = _MOIUC.add_item(_disjunctions(model), disjunction_data)

    _set_ready_to_optimize(model, false)
    return DisjunctionRef(model, idx)
end
function _create_disjunction(
    _error::Function,
    model::JuMP.AbstractModel,
    structure::AbstractArray{<:LogicalVariableRef}, #generalize for containers
    name::String,
    nested::Bool
    )
    vect_structure = [v for v in Iterators.Flatten(structure)]
    return _create_disjunction(_error, model, vect_structure, name, nested)
end

# Disjunction build for unnested disjunctions
function _disjunction(
    _error::Function,
    model::M,
    structure::AbstractArray{<:LogicalVariableRef}, #generalize for containers
    name::String;
    exactly1::Bool = true,
    extra_kwargs...
    ) where {M <: JuMP.AbstractModel}
    # check for unneeded keywords
    for (kwarg, _) in extra_kwargs
        _error("Unrecognized keyword argument $kwarg.")
    end
    # create the disjunction
    dref = _create_disjunction(_error, model, structure, name, false)
    # add the exactly one constraint if desired
    if exactly1 && !any(has_logical_complement.(structure))
        lvars = JuMP.constraint_object(dref).indicators
        func = JuMP.model_convert.(model, Any[1, lvars...])
        set = _MOIExactly(length(lvars) + 1)
        cref = JuMP.add_constraint(model, JuMP.VectorConstraint(func, set))
        gdp_data(model).exactly1_constraints[dref] = cref
    end
    return dref
end

# Fallback disjunction build for nonvector structure
function _disjunction(
    _error::Function,
    model::JuMP.AbstractModel,
    structure,
    name::String,
    args...;
    kwargs...
    )
    _error("Unrecognized disjunction input structure.")
end

# Disjunction build for nested disjunctions
function _disjunction(
    _error::Function,
    model::M,
    structure::AbstractArray{<:LogicalVariableRef},
    name::String,
    tag::Disjunct;
    exactly1::Bool = true,
    extra_kwargs...
    ) where {M <: JuMP.AbstractModel}
    # check for unneeded keywords
    for (kwarg, _) in extra_kwargs
        _error("Unrecognized keyword argument $kwarg.")
    end
    # check that no logical complement is used
    if any(has_logical_complement.(structure))
        _error("Logical complement variables are not supported for " *
               "use in nested disjunctions.")
    end
    # create the disjunction
    dref = _create_disjunction(_error, model, structure, name, true)
    obj = constraint_object(dref)
    _add_indicator_var(_DisjunctConstraint(obj, tag.indicator), dref, model)
    # add the exactly one constraint if desired
    if exactly1 && !any(has_logical_complement.(structure))
        lvars = JuMP.constraint_object(dref).indicators
        func = LogicalVariableRef{M}[tag.indicator, lvars...]
        set = _MOIExactly(length(lvars) + 1)
        cref = JuMP.add_constraint(model, JuMP.VectorConstraint(func, set))
        gdp_data(model).exactly1_constraints[dref] = cref
    end
    return dref
end

# General fallback for additional arguments
function _disjunction(
    _error::Function,
    model::JuMP.AbstractModel,
    structure::AbstractArray{<:LogicalVariableRef},
    name::String,
    extra...;
    kwargs...
    )
    for arg in extra
        _error("Unrecognized argument `$arg`.")
    end
end

"""
    disjunction(
        model::JuMP.AbstractModel,
        disjunct_indicators::Vector{LogicalVariableRef},
        [nested_tag::Disjunct],
        [name::String = ""];
        [exactly1::Bool = true]
    )

Create a disjunction comprised of disjuncts with indicator variables `disjunct_indicators`
and add it to `model`. For nested disjunctions, the `nested_tag` is required to indicate
which disjunct it will be part of in the parent disjunction. By default, `exactly1` adds
a constraint of the form `@constraint(model, disjunct_indicators in Exactly(1))` only
allowing one of the disjuncts to be selected; this is required for certain reformulations like
[`Hull`](@ref). For nested disjunctions, `exactly1` creates a constraint of the form
`@constraint(model, disjunct_indicators in Exactly(nested_tag.indicator))`.
To conveniently generate many disjunctions at once, see [`@disjunction`](@ref)
and [`@disjunctions`](@ref).
"""
function disjunction(
    model::JuMP.AbstractModel,
    disjunct_indicators,
    name::String = "",
    extra...;
    kwargs...
)
    return _disjunction(error, model, disjunct_indicators, name, extra...; kwargs...)
end
function disjunction(
    model::JuMP.AbstractModel,
    disjunct_indicators,
    nested_tag::Disjunct,
    name::String = "",
    extra...;
    kwargs...
)
    return _disjunction(error, model, disjunct_indicators, name, nested_tag, extra...; kwargs...)
end

################################################################################
#                              LOGICAL CONSTRAINTS
################################################################################
"""
    function JuMP.build_constraint(
        _error::Function,
        func::AbstractVector{T},
        set::S
    ) where {T <: LogicalVariableRef, S <: Union{Exactly, AtLeast, AtMost}}

Extend `JuMP.build_constraint` to add logical cardinality constraints to a [`GDPModel`](@ref).
This in combination with `JuMP.add_constraint` enables the use of
`@constraint(model, [name], logical_expr in set)`, where set can be either of the following
cardinality sets: `AtLeast(n)`, `AtMost(n)`, or `Exactly(n)`.

## Example

To select exactly 1 logical variable `Y` to be `true`, do
(the same can be done with `AtLeast(n)` and `AtMost(n)`):

```julia
using DisjunctiveProgramming
model = GDPModel();
@variable(model, Y[i = 1:2], LogicalVariable);
@constraint(model, [Y[1], Y[2]] in Exactly(1));
```
"""
function JuMP.build_constraint( # Cardinality logical constraint
    _error::Function,
    func::AbstractVector{T}, # allow any vector-like JuMP container
    set::S # TODO: generalize to allow CP sets from MOI
) where {T <: LogicalVariableRef, S <: Union{Exactly{Int}, AtLeast{Int}, AtMost{Int}}}
    new_set = _jump_to_moi_selector(set)(length(func) + 1)
    new_func = Union{Number, T}[set.value, func...]
    return JuMP.VectorConstraint(new_func, new_set) # model_convert will make it an AbstractJuMPScalar
end
function JuMP.build_constraint( # Cardinality logical constraint
    _error::Function,
    func::AbstractVector{T}, # allow any vector-like JuMP container
    set::S # TODO: generalize to allow CP sets from MOI
) where {T <: LogicalVariableRef, S <: Union{Exactly, AtLeast, AtMost}}
    new_set = _jump_to_moi_selector(set)(length(func) + 1)
    new_func = [set.value, func...] # will be a vector of type LogicalVariableRef
    return JuMP.VectorConstraint(new_func, new_set)
end
function JuMP.build_constraint( # Cardinality logical constraint
    _error::Function,
    func::AbstractVector,
    set::S # TODO: generalize to allow CP sets from MOI
) where {S <: Union{Exactly, AtLeast, AtMost}}
    _error("Selector constraints can only be applied to a Vector or Container of LogicalVariableRefs or logical expressions.")
end

# Fallback for Affine/Quad expressions
function JuMP.build_constraint(
    _error::Function,
    expr::Union{JuMP.GenericAffExpr{C, <:LogicalVariableRef}, JuMP.GenericQuadExpr{C, <:LogicalVariableRef}},
    set::_MOI.AbstractScalarSet
) where {C}
    _error("Cannot add, subtract, or multiply with logical variables.")
end

# Fallback for other set types
function JuMP.build_constraint(
    _error::Function,
    expr::Union{LogicalVariableRef, _LogicalExpr},
    set::_MOI.AbstractScalarSet
)
    _error("Invalid set `$set` for logical constraint.")
end

# Helper function to enable proper dispatching
function _add_logical_constraint(
    model::M,
    c::JuMP.ScalarConstraint{_LogicalExpr{M}, S},
    name
    ) where {M, S <: Union{MOI.EqualTo{Bool}, JuMP.SkipModelConvertScalarSetWrapper{MOI.EqualTo{Bool}}}}
    # check the constraint out
    is_gdp_model(model) || error("Can only add logical constraints to `GDPModel`s.")
    set = JuMP.moi_set(c)
    func = JuMP.jump_function(c)
    JuMP.check_belongs_to_model(func, model)
    _check_logical_expression(func)
    # add negation if needed
    if !set.value
        func = _LogicalExpr{M}(:!, func)
        set = _MOI.EqualTo{Bool}(true)
    end
    # add the constraint
    new_c = JuMP.ScalarConstraint(func, set) # we have guarranteed that set.value = true
    constr_data = ConstraintData(new_c, name)
    idx = _MOIUC.add_item(_logical_constraints(model), constr_data)
    _set_ready_to_optimize(model, false)
    return LogicalConstraintRef(model, idx)
end

function _add_logical_constraint(
    model::M,
    c::JuMP.ScalarConstraint{_LogicalExpr{M}, S},
    name
    ) where {M, S}
    error("Unexpected set `$(JuMP.moi_set(c))` for logical constraint. Use the syntax " *
          "`@constraint(model, logical_expr := true)`.")
end

# Check that logical expression is valid
function _check_logical_expression(ex)
    _check_logical_expression_literal(ex)
    _check_logical_expression_operator(ex)
end
function _check_logical_expression_literal(ex::_LogicalExpr)
    if _isa_literal(ex)
        error("Cannot define constraint on single logical variable, use `fix` instead.")
    end
end
function _check_logical_expression_operator(ex)
    return
end
function _check_logical_expression_operator(ex::_LogicalExpr)
    if !(ex.head in _LogicalOperatorHeads)
        error("Unrecognized logical operator `$(ex.head)`.")
    end
    for a in ex.args
        _check_logical_expression_operator(a)
    end
    return
end

"""
    function JuMP.add_constraint(
        model::JuMP.GenericModel,
        c::JuMP.ScalarConstraint{_LogicalExpr, MOI.EqualTo{Bool}},
        name::String = ""
    )

Extend `JuMP.add_constraint` to allow creating logical proposition constraints
for a [`GDPModel`](@ref) with the `@constraint` macro. Users should define
logical constraints via the syntax `@constraint(model, logical_expr := true)`.
"""
function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{_LogicalExpr{M}, S},
    name::String = ""
    ) where {S, M <: JuMP.GenericModel} # S <: JuMP.SkipModelConvertScalarSetWrapper{MOI.EqualTo{Bool}} or MOI.EqualTo{Bool}
   return _add_logical_constraint(model, c, name)
end

function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{LogicalVariableRef{M}, S},
    name::String = ""
    ) where {M <: JuMP.GenericModel, S} # S <: JuMP.SkipModelConvertScalarSetWrapper{MOI.EqualTo{Bool}} or MOI.EqualTo{Bool}
    error("Cannot define constraint on single logical variable, use `fix` instead.")
end
function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{GenericAffExpr{C, LogicalVariableRef{M}}, S},
    name::String = ""
    ) where {M <: JuMP.GenericModel, S, C}
    error("Cannot add, subtract, or multiply with logical variables.")
end
function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{GenericQuadExpr{C, LogicalVariableRef{M}}, S},
    name::String = ""
    ) where {M <: JuMP.GenericModel, S, C}
    error("Cannot add, subtract, or multiply with logical variables.")
end

# Define method for adding cardinality constraints (needed to define multiple methods to avoid ambiguous dispatch)
function _add_cardinality_constraint(model, c, name)
    is_gdp_model(model) || error("Can only add logical constraints to `GDPModel`s.")
    func = JuMP.jump_function(c)
    JuMP.check_belongs_to_model.(filter(Base.Fix2(isa, JuMP.AbstractJuMPScalar), func), model)
    # TODO maybe do some formatting on `c` to ensure the types are what we expect later --> build_constraint forces formatting now
    constr_data = ConstraintData(c, name)
    idx = _MOIUC.add_item(_logical_constraints(model), constr_data)
    _set_ready_to_optimize(model, false)
    return LogicalConstraintRef(model, idx)
end

"""
    function JuMP.add_constraint(
        model::JuMP.GenericModel,
        c::VectorConstraint{<:F, S},
        name::String = ""
    ) where {F <: Vector{<:LogicalVariableRef}, S <: AbstractCardinalitySet}

Extend `JuMP.add_constraint` to allow creating logical cardinality constraints
for a [`GDPModel`](@ref) with the `@constraint` macro.
"""
function JuMP.add_constraint(
    model::JuMP.GenericModel,
    c::JuMP.VectorConstraint{F, S},
    name::String = ""
    ) where {F, S <: AbstractCardinalitySet}
    return _add_cardinality_constraint(model, c, name)
end
# TODO create bridges for MOI sets for and use BridgeableConstraint with build_constraint
