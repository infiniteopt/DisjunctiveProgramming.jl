################################################################################
#                              DISJUNCTION SET
################################################################################
"""
    SupportedInnerSet

Union of the scalar MOI sets allowed as constraint-row sets inside a
[`DisjunctionSet`](@ref): `MOI.LessThan{Float64}`,
`MOI.GreaterThan{Float64}`, `MOI.EqualTo{Float64}`, and
`MOI.Interval{Float64}`. Solvers consuming `DisjunctionSet` can use
this union to declare or check inner-set support.
"""
const SupportedInnerSet = Union{
    _MOI.LessThan{Float64},
    _MOI.GreaterThan{Float64},
    _MOI.EqualTo{Float64},
    _MOI.Interval{Float64}
}

"""
    DisjunctionSet(inner_sets::Vector{<:Vector})

The vector set of a disjunction with `length(inner_sets)` disjuncts.
A constraint function in this set stacks the disjunction's activation
expression, one indicator component per disjunct, and the constraint
rows of each disjunct in order:
`[p, z_1, ..., z_k, rows of disjunct 1, ..., rows of disjunct k]`,
where disjunct `i` owns `length(inner_sets[i])` rows. A point is in
the set when the indicators sum to the activation value and every
disjunct whose indicator equals 1 has its rows in their scalar sets.

A top-level disjunction has the constant activation `1`, so exactly
one disjunct is active. A nested disjunction's activation is the
indicator expression of its parent disjunct, so it selects exactly one
disjunct while the parent is active and is vacuous otherwise.
Indicator components must be affine in binary (`MOI.ZeroOne`)
variables; a plain binary variable and its `1 - z` complement are both
valid.

Use [`num_disjuncts`](@ref), [`activation_index`](@ref),
[`indicator_indices`](@ref), and [`row_indices`](@ref) to locate the
components of a constraint function in this set.

Supported inner sets: `MOI.LessThan{Float64}`,
`MOI.GreaterThan{Float64}`, `MOI.EqualTo{Float64}`,
`MOI.Interval{Float64}`.
"""
struct DisjunctionSet <: _MOI.AbstractVectorSet
    inner_sets::Vector{Vector{_MOI.AbstractScalarSet}}
    function DisjunctionSet(inner_sets::Vector{<:Vector})
        isempty(inner_sets) && throw(ArgumentError(
            "A `DisjunctionSet` requires at least one disjunct."))
        for sets in inner_sets, set in sets
            set isa SupportedInnerSet || throw(ArgumentError(
                "Unsupported inner set `$set` in `DisjunctionSet`."))
        end
        return new([_MOI.AbstractScalarSet[set for set in sets]
            for sets in inner_sets])
    end
end

"""
    num_disjuncts(set::DisjunctionSet)

Return the number of disjuncts of the disjunction.
"""
num_disjuncts(set::DisjunctionSet) = length(set.inner_sets)

"""
    activation_index(set::DisjunctionSet)

Return the component index of the disjunction's activation expression
within a constraint function in `set`.
"""
activation_index(::DisjunctionSet) = 1

"""
    indicator_indices(set::DisjunctionSet)

Return the component range of the disjunct indicator expressions
within a constraint function in `set`.
"""
indicator_indices(set::DisjunctionSet) = 1 .+ (1:num_disjuncts(set))

"""
    row_indices(set::DisjunctionSet, i::Int)

Return the component range of disjunct `i`'s constraint rows within a
constraint function in `set`.
"""
function row_indices(set::DisjunctionSet, i::Int)
    offset = 1 + num_disjuncts(set) +
        sum(length(set.inner_sets[j]) for j in 1:(i - 1); init = 0)
    return offset .+ (1:length(set.inner_sets[i]))
end

function _MOI.dimension(set::DisjunctionSet)
    return 1 + num_disjuncts(set) + sum(length, set.inner_sets)
end

Base.copy(set::DisjunctionSet) = DisjunctionSet(set.inner_sets)

function Base.:(==)(a::DisjunctionSet, b::DisjunctionSet)
    return a.inner_sets == b.inner_sets
end

function Base.hash(set::DisjunctionSet, h::UInt)
    return hash(set.inner_sets, hash(:DisjunctionSet, h))
end
