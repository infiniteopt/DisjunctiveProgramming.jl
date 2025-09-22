# Utilities to test macro error exception
# Taken from https://github.com/jump-dev/JuMP.jl/blob/master/test/utilities.jl
function strip_line_from_error(err::ErrorException)
    return ErrorException(replace(err.msg, r"^At.+\:[0-9]+\: `@" => "In `@"))
end
strip_line_from_error(err::LoadError) = strip_line_from_error(err.error)
strip_line_from_error(err) = err
macro test_macro_throws(errortype, m)
    quote
        @test_throws(
            $(esc(strip_line_from_error(errortype))),
            try
                @eval $m
            catch err
                throw(strip_line_from_error(err))
            end
        )
    end
end

# Helper function to test IO methods work correctly
function show_test(mode, obj, exp_str::String; repl=:both)
    if mode == MIME("text/plain")
        repl != :show  && @test sprint(print, obj) == exp_str
        repl != :print && @test sprint(show,  obj) == exp_str
    else
        @test sprint(show, "text/latex", obj) == exp_str
    end
end

# Helper function for IO methods with different possibilities
function show_test(mode, obj, exp_str::Vector{String}; repl=:both)
    if mode == MIME("text/plain")
        repl != :show  && @test sprint(print, obj) in exp_str
        repl != :print && @test sprint(show,  obj) in exp_str
    else
        @test sprint(show, "text/latex", obj) in exp_str
    end
end

# Helper functions to prepare variable bounds without reformulating
function prep_bounds(vref, model, method)
    if requires_variable_bound_info(method)
        DP._variable_bounds(model)[vref] = set_variable_bound_info(vref, method)
    end
    return
end
function prep_bounds(vrefs::Vector, model, method)
    for vref in vrefs
        prep_bounds(vref, model, method)
    end
    return
end
function clear_bounds(model)
    empty!(DP._variable_bounds(model))
    return
end

# Prepare helpful test types 
struct BadVarRef <: JuMP.AbstractVariableRef end
struct DummyReformulation <: AbstractReformulationMethod end

# Define types/methods to test using DP with extension models
struct MyVar{I} <: JuMP.AbstractVariable
    i::I
end
mutable struct MyModel <: AbstractModel
    vars::Vector{MyVar}
    deleted::Set{Int}
    cons::Vector{Any}
    ext::Dict{Symbol, Any}
    optimize_hook::Any
    obj_dict::Dict{Symbol, Any}
    function MyModel()
        return new(MyVar[], Set{Int}(), [], Dict{Symbol, Any}(), nothing, Dict{Symbol, Any}())
    end
end
struct MyVarRef <: AbstractVariableRef
    m::MyModel
    i::Int
end
struct MyConRef
    m::MyModel
    i::Int
end
JuMP.variable_ref_type(::Type{MyModel}) = MyVarRef
function JuMP.set_optimize_hook(m::MyModel, f) 
    m.optimize_hook = f
end
JuMP.object_dictionary(model::MyModel) = model.obj_dict
Base.broadcastable(model::MyModel) = Ref(model)
function JuMP.build_variable(::Function, info::VariableInfo, tag::Type{MyVar})
    return MyVar(Dict{Symbol, Any}(n => getproperty(info, n) for n in fieldnames(VariableInfo)))
end
function JuMP.add_variable(model::MyModel, v::MyVar, name::String = "")
    push!(model.vars, v)
    v.i[:name] = name
    return MyVarRef(model, length(model.vars))
end
function JuMP.add_variable(model::MyModel, v::ScalarVariable, name::String = "")
    new_var = MyVar(Dict{Symbol, Any}(n => getproperty(v.info, n) for n in fieldnames(VariableInfo)))
    push!(model.vars, new_var)
    new_var.i[:name] = name
    return MyVarRef(model, length(model.vars))
end
JuMP.is_valid(m::MyModel, v::MyVarRef) = m === v.m && !(v.i in v.m.deleted)
Base.broadcastable(v::MyVarRef) = Ref(v)
Base.length(::MyVarRef) = 1
Base.broadcastable(c::MyConRef) = Ref(c)
Base.length(::MyConRef) = 1
Base.:(==)(v::MyVarRef, w::MyVarRef) = v.m === w.m && v.i == w.i
JuMP.is_binary(v::MyVarRef) = v.m.vars[v.i].i[:binary]
JuMP.is_integer(v::MyVarRef) = v.m.vars[v.i].i[:integer]
JuMP.has_lower_bound(v::MyVarRef) = v.m.vars[v.i].i[:has_lb]
JuMP.lower_bound(v::MyVarRef) = v.m.vars[v.i].i[:lower_bound]
JuMP.has_upper_bound(v::MyVarRef) = v.m.vars[v.i].i[:has_ub]
JuMP.upper_bound(v::MyVarRef) = v.m.vars[v.i].i[:upper_bound]
JuMP.start_value(v::MyVarRef) = v.m.vars[v.i].i[:start]
JuMP.set_start_value(v::MyVarRef, s) = setindex!(v.m.vars[v.i].i, s, :start)
JuMP.fix_value(v::MyVarRef) = v.m.vars[v.i].i[:fix_value]
JuMP.is_fixed(v::MyVarRef) = v.m.vars[v.i].i[:has_fix]
function JuMP.fix(v::MyVarRef, s) 
    v.m.vars[v.i].i[:fix_value] = s
    v.m.vars[v.i].i[:has_fix] = true
end
function JuMP.unfix(v::MyVarRef) 
    v.m.vars[v.i].i[:fix_value] = NaN
    v.m.vars[v.i].i[:has_fix] = false
end
JuMP.name(v::MyVarRef) = v.m.vars[v.i].i[:name]
JuMP.set_name(v::MyVarRef, n) = setindex!(v.m.vars[v.i].i, n, :name)
JuMP.owner_model(v::MyVarRef) = v.m
function JuMP.delete(m::MyModel, v::MyVarRef)
    push!(v.m.deleted, v.i)
    return
end
JuMP.is_valid(m::MyModel, v::MyConRef) = m === v.m && length(m.cons) >= v.i
Base.:(==)(v::MyConRef, w::MyConRef) = v.m === w.m && v.i == w.i
JuMP.owner_model(v::MyConRef) = v.m
function JuMP.add_constraint(model::MyModel, c::AbstractConstraint, n::String = "")
    push!(model.cons, c)
    return MyConRef(model, length(model.cons))
end
JuMP.name(::MyConRef) = "testcon"
JuMP.constraint_object(c::MyConRef) = c.m.cons[c.i]
function JuMP.add_constraint(
    model::MyModel,
    c::VectorConstraint{F, S},
    name::String = ""
    ) where {F, S <: AbstractCardinalitySet}
    return DP._add_cardinality_constraint(model, c, name)
end
function JuMP.add_constraint(
    model::M,
    c::JuMP.ScalarConstraint{DP._LogicalExpr{M}, S},
    name::String = ""
    ) where {S, M <: MyModel} # S <: JuMP._DoNotConvertSet{MOI.EqualTo{Bool}} or MOI.EqualTo{Bool}
   return DP._add_logical_constraint(model, c, name)
end
DP.requires_disaggregation(::MyVarRef) = true
