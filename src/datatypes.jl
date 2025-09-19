################################################################################
#                              LOGICAL VARIABLES
################################################################################
"""
    LogicalVariableIndex

A type for storing the index of a [`LogicalVariable`](@ref).

**Fields**
- `value::Int64`: The index value.
"""
struct LogicalVariableIndex
    value::Int64
end

"""
    LogicalVariableRef{M <: JuMP.AbstractModel}

A type for looking up logical variables.
"""
struct LogicalVariableRef{M <:JuMP.AbstractModel} <: JuMP.AbstractVariableRef
    model::M
    index::LogicalVariableIndex
end

"""
    LogicalVariable <: JuMP.AbstractVariable

A variable type the logical variables associated with disjuncts in a [`Disjunction`](@ref).

**Fields**
- `fix_value::Union{Nothing, Bool}`: A fixed boolean value if there is one.
- `start_value::Union{Nothing, Bool}`: An initial guess if there is one.
- `logical_complement::Union{Nothing, LogicalVariableRef}`: The logical complement of
   this variable if there is one.
"""
struct LogicalVariable <: JuMP.AbstractVariable 
    fix_value::Union{Nothing, Bool}
    start_value::Union{Nothing, Bool}
    logical_complement::Union{Nothing, LogicalVariableRef}
end

# Wrapper variable type for including arbitrary tags that will be used for 
# creating reformulation variables later on
struct _TaggedLogicalVariable{T} <: JuMP.AbstractVariable
    variable::LogicalVariable
    tag_data::T
end

"""
    Logical{T}

Tag for creating logical variables using `@variable`. Most often this will 
be used to enable the syntax:
```julia
@variable(model, var_expr, Logical, [kwargs...])
```
which creates a [`LogicalVariable`](@ref) that will ultimately be 
reformulated into a binary variable of the form:
```julia
@variable(model, var_expr, Bin, [kwargs...])
```

To include a tag that is used to create the reformulated variables, the syntax 
becomes:
```julia
@variable(model, var_expr, Logical(MyTag()), [kwargs...])
```
which creates a [`LogicalVariable`](@ref) that is associated with `MyTag()` such 
that the reformulation binary variables are of the form:
```julia
@variable(model, var_expr, Bin, MyTag(), [kwargs...])
```
"""
struct Logical{T}
    tag_data::T
end

"""
    LogicalVariableData

A type for storing [`LogicalVariable`](@ref)s and any meta-data they 
possess.

**Fields**
- `variable::LogicalVariable`: The logical variable object.
- `name::String`: The name of the variable.
"""
mutable struct LogicalVariableData
    variable::LogicalVariable
    name::String
end

################################################################################
#                        LOGICAL SELECTOR (CARDINALITY) SETS
################################################################################
# TODO check required methods for AbstractVectorSet: 
# All AbstractVectorSets of type S must implement:
# •  dimension, unless the dimension is
#    stored in the set.dimension field
# •  Utilities.set_dot, unless the dot
#    product between two vectors in the set
#    is equivalent to LinearAlgebra.dot.
"""
    AbstractCardinalitySet <: MOI.AbstractVectorSet

An abstract type for cardinality sets [`_MOIAtLeast`](@ref), [`_MOIExactly`](@ref),
and [`_MOIAtMost`](@ref).
"""
abstract type AbstractCardinalitySet <:_MOI.AbstractVectorSet end

"""
    _MOIAtLeast <: AbstractCardinalitySet

MOI level set for AtLeast constraints, see [`AtLeast`](@ref) for recommended syntax.
"""
struct _MOIAtLeast <: AbstractCardinalitySet
    dimension::Int
end

"""
    _MOIAtMost <: AbstractCardinalitySet

MOI level set for AtMost constraints, see [`AtMost`](@ref) for recommended syntax.
"""
struct _MOIAtMost <: AbstractCardinalitySet
    dimension::Int
end

"""
    _MOIExactly <: AbstractCardinalitySet

MOI level set for Exactly constraints, see [`Exactly`](@ref) for recommended syntax.
"""
struct _MOIExactly <: AbstractCardinalitySet
    dimension::Int
end

# Create our own JuMP level sets to infer the dimension using the expression
"""
    AtLeast{T<:Union{Int,LogicalVariableRef}} <: JuMP.AbstractVectorSet

Convenient alias for using [`_MOIAtLeast`](@ref).
"""
struct AtLeast{T<:Union{Int, LogicalVariableRef}} <: JuMP.AbstractVectorSet
    value::T
end

"""
    AtMost{T<:Union{Int,LogicalVariableRef}} <: JuMP.AbstractVectorSet

Convenient alias for using [`_MOIAtMost`](@ref).
"""
struct AtMost{T<:Union{Int, LogicalVariableRef}} <: JuMP.AbstractVectorSet
    value::T
end

"""
    Exactly <: JuMP.AbstractVectorSet

Convenient alias for using [`_MOIExactly`](@ref).
"""
struct Exactly{T<:Union{Int, LogicalVariableRef}} <: JuMP.AbstractVectorSet
    value::T 
end

# Extend JuMP.moi_set as needed
JuMP.moi_set(::AtLeast, dim::Int) = _MOIAtLeast(dim)
JuMP.moi_set(::AtMost, dim::Int) = _MOIAtMost(dim)
JuMP.moi_set(::Exactly, dim::Int) = _MOIExactly(dim)

################################################################################
#                              LOGICAL CONSTRAINTS
################################################################################
const _LogicalExpr{M} = JuMP.GenericNonlinearExpr{LogicalVariableRef{M}}

"""
    ConstraintData{C <: JuMP.AbstractConstraint}

A type for storing constraint objects in [`GDPData`](@ref) and any meta-data 
they possess.

**Fields**
- `constraint::C`: The constraint.
- `name::String`: The name of the proposition.
"""
mutable struct ConstraintData{C <: JuMP.AbstractConstraint}
    constraint::C
    name::String
end

"""
    LogicalConstraintIndex

A type for storing the index of a logical constraint.

**Fields**
- `value::Int64`: The index value.
"""
struct LogicalConstraintIndex
    value::Int64
end

"""
    LogicalConstraintRef{M <: JuMP.AbstractModel}

A type for looking up logical constraints.
"""
struct LogicalConstraintRef{M <: JuMP.AbstractModel}
    model::M
    index::LogicalConstraintIndex
end

################################################################################
#                              DISJUNCT CONSTRAINTS
################################################################################
"""
    Disjunct

Used as a tag for constraints that will be used in disjunctions. This is done via 
the following syntax:
```julia-repl
julia> @constraint(model, [constr_expr], Disjunct)

julia> @constraint(model, [constr_expr], Disjunct(lvref))
```
where `lvref` is a [`LogicalVariableRef`](@ref) that will ultimately be associated 
with the disjunct the constraint is added to. If no `lvref` is given, then one is 
generated when the disjunction is created.
"""
struct Disjunct{M <: JuMP.AbstractModel}
    indicator::LogicalVariableRef{M}
end

# Create internal type for temporarily packaging constraints for disjuncts
struct _DisjunctConstraint{C <: AbstractConstraint, L <: LogicalVariableRef}
    constr::C
    lvref::L
end

"""
    DisjunctConstraintIndex

A type for storing the index of a [`Disjunct`](@ref).

**Fields**
- `value::Int64`: The index value.
"""
struct DisjunctConstraintIndex
    value::Int64
end

"""
    DisjunctConstraintRef{M <: JuMP.AbstractModel}

A type for looking up disjunctive constraints.
"""
struct DisjunctConstraintRef{M <: JuMP.AbstractModel}
    model::M
    index::DisjunctConstraintIndex
end

################################################################################
#                              DISJUNCTIONS
################################################################################
"""
    Disjunction{M <: JuMP.AbstractModel} <: JuMP.AbstractConstraint

A type for a disjunctive constraint that is comprised of a collection of 
disjuncts of indicated by a unique [`LogicalVariableIndex`](@ref).

**Fields**
- `indicators::Vector{LogicalVariableref}`: The references to the logical variables 
(indicators) that uniquely identify each disjunct in the disjunction.
- `nested::Bool`: Is this disjunction nested within another disjunction?
"""
struct Disjunction{M <: JuMP.AbstractModel} <: JuMP.AbstractConstraint
    indicators::Vector{LogicalVariableRef{M}}
    nested::Bool
end

"""
    DisjunctionIndex

A type for storing the index of a [`Disjunction`](@ref).

**Fields**
- `value::Int64`: The index value.
"""
struct DisjunctionIndex
    value::Int64
end

"""
    DisjunctionRef{M <: JuMP.AbstractModel}

A type for looking up disjunctive constraints.
"""
struct DisjunctionRef{M <: JuMP.AbstractModel}
    model::M
    index::DisjunctionIndex
end

################################################################################
#                              CLEVER DICTS
################################################################################
## Extend the CleverDicts key access methods
# index_to_key
function _MOIUC.index_to_key(::Type{LogicalVariableIndex}, index::Int64)
    return LogicalVariableIndex(index)
end
function _MOIUC.index_to_key(::Type{DisjunctConstraintIndex}, index::Int64)
    return DisjunctConstraintIndex(index)
end
function _MOIUC.index_to_key(::Type{DisjunctionIndex}, index::Int64)
    return DisjunctionIndex(index)
end
function _MOIUC.index_to_key(::Type{LogicalConstraintIndex}, index::Int64)
    return LogicalConstraintIndex(index)
end

# key_to_index
function _MOIUC.key_to_index(key::LogicalVariableIndex)
    return key.value
end
function _MOIUC.key_to_index(key::DisjunctConstraintIndex)
    return key.value
end
function _MOIUC.key_to_index(key::DisjunctionIndex)
    return key.value
end
function _MOIUC.key_to_index(key::LogicalConstraintIndex)
    return key.value
end

################################################################################
#                              SOLUTION METHODS
################################################################################
"""
    AbstractSolutionMethod

An abstract type for solution methods used to solve `GDPModel`s.
"""
abstract type AbstractSolutionMethod end

"""
    AbstractReformulationMethod <: AbstractSolutionMethod

An abstract type for reformulation approaches used to solve `GDPModel`s.
"""
abstract type AbstractReformulationMethod <: AbstractSolutionMethod end

"""
    BigM{T} <: AbstractReformulationMethod

A type for using the big-M reformulation approach for disjunctive constraints.

**Fields**
- `value::T`: Big-M value (default = `1e9`).
- `tight::Bool`: Attempt to tighten the Big-M value (default = `true`)?
"""
struct BigM{T} <: AbstractReformulationMethod
    value::T
    tighten::Bool
    function BigM(val::T = 1e9, tight = true) where {T}
        new{T}(val, tight)
    end
end

"""
    MBM{O} <: AbstractReformulationMethod

A type for using the multiple big-M reformulation approach for disjunctive constraints.

**Fields**
- 'optimizer::O': Optimizer to use when solving mini-models (required).
"""
struct MBM{O} <: AbstractReformulationMethod
    optimizer::O
    
    # Constructor with optimizer (required)
    function MBM(optimizer::O) where {O}
        new{O}(optimizer)
    end
end



"""
    Hull{T} <: AbstractReformulationMethod

A type for using the convex hull reformulation approach for disjunctive 
constraints.

**Fields**
- `value::T`: epsilon value for nonlinear hull reformulations (default = `1e-6`).
"""
struct Hull{T} <: AbstractReformulationMethod
    value::T
    function Hull(ϵ::T = 1e-6) where {T}
        new{T}(ϵ)
    end
end

# temp struct to store variable disaggregations (reset for each disjunction)
mutable struct _Hull{V <: JuMP.AbstractVariableRef, T} <: AbstractReformulationMethod
    value::T
    disjunction_variables::Dict{V, Vector{V}}
    disjunct_variables::Dict{Tuple{V, Union{V, JuMP.GenericAffExpr{T, V}}}, V}
    function _Hull(method::Hull{T}, vrefs::Set{V}) where {T, V <: JuMP.AbstractVariableRef}
        new{V, T}(
            method.value,
            Dict{V, Vector{V}}(vref => V[] for vref in vrefs), 
            Dict{Tuple{V, Union{V, JuMP.GenericAffExpr{T, V}}}, V}()
        )
    end
end

"""
    Indicator <: AbstractReformulationMethod

A type for using indicator constraint approach for linear disjunctive constraints.
"""
struct Indicator <: AbstractReformulationMethod end

################################################################################
#                              GDP Data
################################################################################
"""
    GDPData{M <: JuMP.AbstractModel, V <: JuMP.AbstractVariableRef, CrefType, ValueType}

The core type for storing information in a [`GDPModel`](@ref).
"""
mutable struct GDPData{M <: JuMP.AbstractModel, V <: JuMP.AbstractVariableRef, C, T}
    # Objects
    logical_variables::_MOIUC.CleverDict{LogicalVariableIndex, LogicalVariableData}
    logical_constraints::_MOIUC.CleverDict{LogicalConstraintIndex, ConstraintData}
    disjunct_constraints::_MOIUC.CleverDict{DisjunctConstraintIndex, ConstraintData}
    disjunctions::_MOIUC.CleverDict{DisjunctionIndex, ConstraintData{Disjunction{M}}}

    # Exactly one constraint mappings
    exactly1_constraints::Dict{DisjunctionRef{M}, LogicalConstraintRef{M}}

    # Indicator variable mappings
    indicator_to_binary::Dict{LogicalVariableRef{M}, Union{V, JuMP.GenericAffExpr{T, V}}}
    indicator_to_constraints::Dict{LogicalVariableRef{M}, Vector{Union{DisjunctConstraintRef{M}, DisjunctionRef{M}}}}
    constraint_to_indicator::Dict{Union{DisjunctConstraintRef{M}, DisjunctionRef{M}}, LogicalVariableRef{M}} # needed for deletion

    # Helpful metadata for most reformulations (not just one of them)
    variable_bounds::Dict{V, Tuple{T, T}}

    # Reformulation variables and constraints
    reformulation_variables::Vector{V}
    reformulation_constraints::Vector{C}

    # Solution data
    solution_method::Union{Nothing, AbstractSolutionMethod}
    ready_to_optimize::Bool

    # Default constructor
    function GDPData{M, V, C}() where {M <: JuMP.AbstractModel, V <: JuMP.AbstractVariableRef, C}
        T = JuMP.value_type(M)
        new{M, V, C, T}(_MOIUC.CleverDict{LogicalVariableIndex, LogicalVariableData}(),
            _MOIUC.CleverDict{LogicalConstraintIndex, ConstraintData}(),
            _MOIUC.CleverDict{DisjunctConstraintIndex, ConstraintData}(),
            _MOIUC.CleverDict{DisjunctionIndex, ConstraintData{Disjunction{M}}}(),
            Dict{DisjunctionRef{M}, LogicalConstraintRef{M}}(),
            Dict{LogicalVariableRef{M}, Union{V, JuMP.GenericAffExpr{T, V}}}(),
            Dict{LogicalVariableRef{M}, Vector{Union{DisjunctConstraintRef{M}, DisjunctionRef{M}}}}(),
            Dict{Union{DisjunctConstraintRef{M}, DisjunctionRef{M}}, LogicalVariableRef{M}}(),
            Dict{V, Tuple{T, T}}(),
            Vector{V}(),
            Vector{C}(),
            nothing,
            false,
        )
    end
end

################################################################################
#                              VARIABLE INFO
################################################################################
"""
    VariableProperties

A type for storing variable properties and attributes that can be applied to JuMP variables.
This is used to capture and transfer variable information between models during reformulation.

**Fields**
- `name::String`: The variable name.
- `is_fixed::Bool`: Whether the variable is fixed to a specific value.
- `is_binary::Bool`: Whether the variable is constrained to be binary.
- `is_integer::Bool`: Whether the variable is constrained to be integer.
- `lower_bound::Union{Nothing, Float64}`: The lower bound of the variable if it exists.
- `upper_bound::Union{Nothing, Float64}`: The upper bound of the variable if it exists.
- `fix_value::Union{Nothing, Float64}`: The fixed value of the variable if it is fixed.
- `start_value::Union{Nothing, Float64}`: The start value (initial guess) for the variable if provided.
"""
mutable struct VariableProperties
    name::String
    is_fixed::Bool
    is_binary::Bool
    is_integer::Bool
    lower_bound::Union{Nothing, Float64}
    upper_bound::Union{Nothing, Float64}
    fix_value::Union{Nothing, Float64}
    start_value::Union{Nothing, Float64}
    function VariableProperties(vref::JuMP.AbstractVariableRef)
        new(
            JuMP.name(vref),
            JuMP.is_fixed(vref),
            JuMP.is_binary(vref),
            JuMP.is_integer(vref),
            JuMP.has_lower_bound(vref) ? JuMP.lower_bound(vref) : nothing,
            JuMP.has_upper_bound(vref) ? JuMP.upper_bound(vref) : nothing,
            JuMP.is_fixed(vref) ? JuMP.fix_value(vref) : nothing,
            JuMP.has_start_value(vref) ? JuMP.start_value(vref) : nothing
        )   
    end
    function VariableProperties()
        new("", false, false, false, nothing, nothing, nothing, nothing)
    end
end