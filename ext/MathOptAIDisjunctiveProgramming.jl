module MathOptAIDisjunctiveProgramming

import MathOptAI
import DisjunctiveProgramming as DP
import JuMP
const _MOI = JuMP.MOI

################################################################################
#                            DISJUNCTIVE PREDICTOR
################################################################################
# A MathOptAI predictor to embed as a GDP disjunction
struct _Disjunctive{P <: MathOptAI.AbstractPredictor} <:
    MathOptAI.AbstractPredictor
    predictor::P
end
DP.Disjunctive(predictor) = _Disjunctive(predictor)

################################################################################
#                              DECISION TREES
################################################################################
# Leaf => root to leaf split rows as (feature, set) pairs; the left bound is
# threshold - atol, MathOptAI's disjoint-branch convention
_leaf_paths(leaf, path) = [leaf => path]
function _leaf_paths(
    node::MathOptAI.BinaryDecisionTree,
    path = Pair{Int, _MOI.AbstractScalarSet}[]
    )
    threshold = Float64(node.feat_value)
    left = node.feat_id => _MOI.LessThan(threshold - node.atol)
    right = node.feat_id => _MOI.GreaterThan(threshold)
    return vcat(_leaf_paths(node.lhs, [path; left]),
        _leaf_paths(node.rhs, [path; right]))
end

# Leaf rule as an `Affine`: a constant leaf has zero coefficients
_affine_leaf(leaf::Real, num_inputs) =
    MathOptAI.Affine(zeros(1, num_inputs), [float(leaf)])
_affine_leaf(leaf::MathOptAI.Affine, num_inputs) = leaf

# Bounds of an input read through JuMP, since InfiniteOpt's MathOptAI hook
# reports none for its variables; an infinite parameter gives its domain
function _input_bounds(x::JuMP.AbstractVariableRef)
    JuMP.is_fixed(x) && return JuMP.fix_value(x), JuMP.fix_value(x)
    JuMP.is_binary(x) && return 0.0, 1.0
    lower = JuMP.has_lower_bound(x) ? JuMP.lower_bound(x) : missing
    upper = JuMP.has_upper_bound(x) ? JuMP.upper_bound(x) : missing
    return lower, upper
end
_input_bounds(x) = MathOptAI.get_variable_bounds(x)

# Envelope of the leaf rules over the input box; `missing` when an input
# with a nonzero coefficient is unbounded, which Hull then rejects itself
function _output_bounds(leaves, x)
    bounds = _input_bounds.(x)
    lower, upper = Inf, -Inf
    for leaf in leaves
        leaf_lower = leaf_upper = only(leaf.b)
        for (coeff, (input_lower, input_upper)) in zip(leaf.A, bounds)
            iszero(coeff) && continue
            leaf_lower += coeff * (coeff > 0 ? input_lower : input_upper)
            leaf_upper += coeff * (coeff > 0 ? input_upper : input_lower)
        end
        lower, upper = min(lower, leaf_lower), max(upper, leaf_upper)
    end
    return lower, upper
end

function MathOptAI.add_predictor(
    model::JuMP.AbstractModel,
    predictor::_Disjunctive{<:MathOptAI.BinaryDecisionTree},
    x::Vector
    )
    paths = _leaf_paths(predictor.predictor)
    leaves = [_affine_leaf(leaf, length(x)) for (leaf, _) in paths]
    y = only(MathOptAI.add_variables(model, x, 1, "moai_Disjunctive"))
    cons = Any[]
    MathOptAI.set_variable_bounds(cons, y, _output_bounds(leaves, x)...)
    # indicators vary over the parameters of y (if any), so each point
    # picks its own leaf
    tag = DP.VariableProperties(y).variable_type
    logical = isnothing(tag) ? DP.Logical : DP.Logical(tag)
    indicators = JuMP.@variable(model, [1:length(paths)], logical,
        base_name = "moai_Disjunctive_Z")
    for (indicator, (_, path), leaf) in zip(indicators, paths, leaves)
        for (feature, set) in path # affine row, the form DP.jl reformulates
            push!(cons, JuMP.@constraint(model, 1 * x[feature] in set,
                DP.Disjunct(indicator)))
        end
        push!(cons, JuMP.@constraint(model,
            y == only(leaf.A * x) + only(leaf.b), DP.Disjunct(indicator)))
    end
    push!(cons, DP.disjunction(model, indicators))
    return [y], MathOptAI.Formulation(predictor, Any[y; indicators], cons)
end

end # module
