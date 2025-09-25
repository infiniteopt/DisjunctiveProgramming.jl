################################################################################
#                               UTILITY METHODS
################################################################################
# Requred for extensions to MOI.AbstractVectorSet
# function _MOI.Utilities.set_dot(x::AbstractVector, y::AbstractVector, set::DisjunctionSet)
#     return LinearAlgebra.dot(x, y) # TODO figure out what we should actually do here
# end

# TODO create a bridge for `DisjunctionSet`

# TODO create helper method to unpack DisjunctionSet at the MOI side of things

################################################################################
#                            REFRORMULATION METHODS
################################################################################
# Helper methods to handle recursively flattening the disjuncts
function _constr_set!(model, funcs, con::JuMP.AbstractConstraint)
    append!(funcs, JuMP.jump_function(con))
    return JuMP.moi_set(con)
end
function _constr_set!(model, funcs, con::Disjunction)
    inner_funcs, set = _disjunction_to_set(model, con)
    append!(funcs, inner_funcs)
    return set
end

# Create the vectors needed for a disjunction vector constraint
function _disjunction_to_set(model::JuMP.Model, d::Disjunction)
    # allocate memory for the storage vectors
    num_disjuncts = length(d.indicators)
    constr_mappings = _indicator_to_constraints(model)
    num_constrs = sum(length(constr_mappings[lvref]) for lvref in d.indicators)
    funcs = sizehint!(JuMP.AbstractJuMPScalar[], num_disjuncts + num_constrs)
    sets = Vector{Vector{_MOI.AbstractSet}}(undef, num_disjuncts)
    d_idxs = Vector{Int}(undef, num_disjuncts)
    # iterate over the underlying disjuncts to fill in the storage vectors
    for (i, lvref) in enumerate(d.indicators)
        push!(funcs, _indicator_to_binary(model)[lvref])
        d_idxs[i] = length(funcs)
        crefs = constr_mappings(model)[lvref]
        sets[i] = map(c -> _constr_set!(model, funcs, JuMP.constraint_object(c)), crefs)
    end
    # convert the `sets` type to be concrete if possible (TODO benchmark if this is worth it)
    SetType = typeof(first(sets))
    if SetType != Vector{_MOI.AbstractSet} && all(s -> s isa SetType, sets) 
        sets = convert(SetType, sets)
    end
    return funcs, DisjunctionSet(length(funcs), d_idxs, sets)
end

# Extend the disjunction reformulation
function reformulate_disjunction(
    model::JuMP.Model, 
    d::Disjunction, 
    ::MOIDisjunction
    )
    funcs, set = _disjunction_to_set(model, d)
    return [JuMP.VectorConstraint(funcs, set, JuMP.VectorShape())]
end