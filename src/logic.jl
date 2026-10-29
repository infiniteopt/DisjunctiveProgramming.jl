################################################################################
#                              LOGIC OPERATORS
################################################################################
function _op_fallback(name)
    error("`$name` is only supported for logical expressions")
end

# Define all the logical operators
const _LogicalOperatorHeads = (:(==), :(=>), :||, :&&, :!)
for (name, alt, head) in (
    (:⇔, :iff, :(==)), # \Leftrightarrow + tab
    (:⟹, :implies, :(=>)) # Longrightarrow + tab
    )
    # make operators
    @eval begin 
        const $name = NonlinearOperator((vs...) -> _op_fallback($(Meta.quot(name))), $(Meta.quot(head)))
        const $alt = NonlinearOperator((vs...) -> _op_fallback($(Meta.quot(alt))), $(Meta.quot(head)))
    end
end
for (name, alt, head, func) in (
    (:∨, :logical_or, :||, :(|)), # \vee + tab
    (:∧, :logical_and, :&&, :(&)), # \wedge + tab
    (:¬, :logical_not, :!, :(!)) # \neg + tab
    )
    # make operators
    @eval begin 
        const $name = NonlinearOperator($func, $(Meta.quot(head)))
        const $alt = NonlinearOperator($func, $(Meta.quot(head)))
    end
end

################################################################################
#                            CONJUNCTIVE NORMAL FORM
################################################################################
function _to_cnf(lexpr::_LogicalExpr)
    #NOTE: some redundant constraints may be created in the process.
    #   For example A ∨ ¬B ∨ B is always true and is reformulated 
    #   to the redundant constraint A ≥ 0.
    lexpr |> 
        _eliminate_equivalence |>  
        _eliminate_implication |> 
        _move_negations_inward |> 
        _distribute_and_over_or |>
        _flatten
end

# Eliminate the equivalence operator `⇔` by replacing it with two implications.
function _eliminate_equivalence(lvar::LogicalVariableRef)
    return lvar
end
function _eliminate_equivalence(lexpr::_LogicalExpr{M}) where {M}
    if lexpr.head == :(==)
        A = _eliminate_equivalence(lexpr.args[1])
        if length(lexpr.args) > 2 
            nested = _LogicalExpr{M}(:(==), Vector{Any}(lexpr.args[2:end]))
            B = _eliminate_equivalence(nested)
        elseif length(lexpr.args) == 2
            B = _eliminate_equivalence(lexpr.args[2])
        else
            error("The equivalence logic operator must have at least two clauses.")
        end
        new_lexpr = _LogicalExpr{M}(:&&, Any[
            _LogicalExpr{M}(:(=>), Any[A, B]),
            _LogicalExpr{M}(:(=>), Any[B, A])
        ])
    else
        new_lexpr = _LogicalExpr{M}(lexpr.head, Any[
            _eliminate_equivalence(arg) for arg in lexpr.args
        ])
    end
    return new_lexpr
end

# Eliminate the implication operator `⟹` by replacing it with a disjunction.
function _eliminate_implication(lvar::LogicalVariableRef)
    return lvar
end
function _eliminate_implication(lexpr::_LogicalExpr{M}) where {M}
    if lexpr.head == :(=>)
        if length(lexpr.args) != 2 
            error("The implication operator must have two clauses.")
        end
        A = _eliminate_implication(lexpr.args[1])
        B = _eliminate_implication(lexpr.args[2])
        new_lexpr = _LogicalExpr{M}(:||, Any[
            _LogicalExpr{M}(:!, Any[A]),
            B
        ])
    else
        new_lexpr = _LogicalExpr{M}(lexpr.head, Any[
            _eliminate_implication(arg) for arg in lexpr.args
        ])
    end
    return new_lexpr
end

# Move negations inward by applying De Morgan's laws.
function _move_negations_inward(lvar::LogicalVariableRef)
    return lvar
end
function _move_negations_inward(lexpr::_LogicalExpr{M}) where {M}
    if lexpr.head == :!
        if length(lexpr.args) != 1
            error("The negation operator can only have one clause.")
        end
        new_lexpr = _negate(lexpr.args[1])
    else
        new_lexpr = _LogicalExpr{M}(lexpr.head, Any[
            _move_negations_inward(arg) for arg in lexpr.args
        ])
    end
    return new_lexpr
end

function _negate(lvar::LogicalVariableRef{M}) where {M}
    return _LogicalExpr{M}(:!, Any[lvar])
end
function _negate(lexpr::_LogicalExpr)
    if lexpr.head == :||
        return _negate_or(lexpr)
    elseif lexpr.head == :&&
        return _negate_and(lexpr)
    elseif lexpr.head == :!
        return _negate_negation(lexpr)
    else
        error("Unexpected operator `$(lexpr.head)`in logic expression.")
    end
end

function _negate_or(lexpr::_LogicalExpr{M}) where {M}
    if length(lexpr.args) < 2 
        error("The OR operator must have at least two clauses.")
    end
    return _LogicalExpr{M}(:&&, Any[ #flip OR to AND
        _move_negations_inward(_LogicalExpr{M}(:!, Any[arg]))
        for arg in lexpr.args
    ])
end

function _negate_and(lexpr::_LogicalExpr{M}) where {M}
    if length(lexpr.args) < 2 
        error("The AND operator must have at least two clauses.")
    end
    return _LogicalExpr{M}(:||, Any[ #flip AND to OR
        _move_negations_inward(_LogicalExpr{M}(:!, Any[arg]))
        for arg in lexpr.args
    ])
end

function _negate_negation(lexpr::_LogicalExpr)
    if length(lexpr.args) != 1
        error("The negation operator can only have 1 clause.")
    end
    return _move_negations_inward(lexpr.args[1])
end

function _distribute_and_over_or(lvar::LogicalVariableRef)
    return lvar
end
function _distribute_and_over_or(lexpr0::_LogicalExpr{M}) where {M}
    lexpr = _flatten(lexpr0)
    if lexpr.head == :||
        if length(lexpr.args) < 2 
            error("The OR operator must have at least two clauses.")
        end
        loc = findfirst(arg -> arg isa _LogicalExpr ? arg.head == :&& : false, lexpr.args)
        if !isnothing(loc)
            new_lexpr = _LogicalExpr{M}(:&&, Any[
                _distribute_and_over_or(
                    _LogicalExpr{M}(:||, Any[arg_i, lexpr.args[setdiff(1:end,loc)]...])
                )
                for arg_i in lexpr.args[loc].args
            ])
        else
            new_lexpr = lexpr
        end
    else
        new_lexpr = _LogicalExpr{M}(lexpr.head, Any[
            _distribute_and_over_or(arg) for arg in lexpr.args
        ])
    end
    return new_lexpr
end

# Flatten netsed OR / AND operators and replace them with their n-ary form.
#   For example, ∨(∨(A, B), C) is replaced with ∨(A, B, C).
function _flatten(lvar::LogicalVariableRef)
    return lvar
end
function _flatten(lexpr::_LogicalExpr{M}) where {M}
    if lexpr.head in (:&&, :||)
        nary_args = Set{Any}()
        for arg in lexpr.args
            if arg isa LogicalVariableRef
                push!(nary_args, arg)
            elseif _isa_literal(arg)
                push!(nary_args, arg)
            elseif arg.head == lexpr.head
                arg_flat = _flatten(arg)
                for a in arg_flat.args
                    push!(nary_args, _flatten(a))
                end
            else
                arg_flat = _flatten(arg)
                push!(nary_args, arg_flat)
            end
        end
        new_lexpr = _LogicalExpr{M}(lexpr.head, collect(nary_args))
    else 
        new_lexpr = _LogicalExpr{M}(lexpr.head, Any[
            _flatten(arg) for arg in lexpr.args
        ])
    end
    return new_lexpr
end

################################################################################
#                              SELECTOR REFORMULATION
################################################################################
# cardinality constraint reformulation
function _reformulate_selector(
    model::M, 
    func::Vector{JuMP.AbstractJuMPScalar}, 
    set::AbstractCardinalitySet
    ) where {M <: JuMP.AbstractModel}
    aff_type =
        JuMP.GenericAffExpr{JuMP.value_type(M), JuMP.variable_ref_type(M)}
    bvrefs = aff_type[binary_variable(lvref) for lvref in func[2:end]]
    c = JuMP.constant(func[1])
    new_set = _vec_to_scalar_set(set)(c)
    init = zero(JuMP.value_type(M))
    cref = JuMP.@constraint(model, sum(bvrefs, init = init) in new_set)
    push!(_reformulation_constraints(model), cref)
end
function _reformulate_selector(
    model::M, 
    func::Vector{<:LogicalVariableRef}, 
    set::AbstractCardinalitySet
    ) where {M <: JuMP.AbstractModel}
    aff_type =
        JuMP.GenericAffExpr{JuMP.value_type(M), JuMP.variable_ref_type(M)}
    bvref, bvrefs... = aff_type[binary_variable(lvref) for lvref in func]
    new_set = _vec_to_scalar_set(set)(0)
    init = zero(JuMP.value_type(M))
    cref = JuMP.@constraint(model, sum(bvrefs, init = init) - bvref in new_set)
    push!(_reformulation_constraints(model), cref)
end

################################################################################
#                              PROPOSITION REFORMULATION
################################################################################
function _reformulate_proposition(model::JuMP.AbstractModel, lexpr::_LogicalExpr)
    expr = _to_cnf(lexpr)
    if expr.head == :&&
        for arg in expr.args
            _add_reformulated_proposition(model, arg)
        end
    elseif expr.head in (:||, :!) && all(_isa_literal.(expr.args))
        _add_reformulated_proposition(model, expr)
    else #NOTE: should never enter the `else` section
        error("Expression $expr was not converted to proper Conjunctive Normal Form.")
    end
end

# helper to determine if an object is a logic literal (i.e. a logic variable or its negation)
_isa_literal(v::LogicalVariableRef) = true
_isa_literal(v::_LogicalExpr) = (v.head == :!) && (length(v.args) == 1) && _isa_literal(v.args[1])
_isa_literal(v) = false

function _add_reformulated_proposition(
    model::JuMP.AbstractModel, 
    arg::Union{LogicalVariableRef, _LogicalExpr}
    )
    func = _reformulate_clause(model, arg)
    if !isempty(func.terms) && !all(iszero.(values(func.terms)))
        cref = JuMP.@constraint(model, func >= 1)
        push!(_reformulation_constraints(model), cref)
    end
    return
end

function _reformulate_clause(model::JuMP.AbstractModel, lvref::LogicalVariableRef)
    func = 1 * binary_variable(lvref)
    return func
end

function _reformulate_clause(model::M, lexpr::_LogicalExpr) where {M <: JuMP.AbstractModel}
    func = zero(JuMP.GenericAffExpr{JuMP.value_type(M), JuMP.variable_ref_type(M)}) #initialize func expression
    if _isa_literal(lexpr)
        JuMP.add_to_expression!(func, 1 - _reformulate_clause(model, lexpr.args[1]))
    elseif lexpr.head == :||
        for literal in lexpr.args
            if literal isa LogicalVariableRef
                JuMP.add_to_expression!(func, _reformulate_clause(model, literal))
            elseif _isa_literal(literal)
                JuMP.add_to_expression!(func, 1 - _reformulate_clause(model, literal.args[1]))
            else
                error("Expression was not converted to proper Conjunctive Normal Form:\n$literal is not a literal.")
            end
        end
    else
        error("Expression was not converted to proper Conjunctive Normal Form:\n$lexpr.")
    end
    return func
end
