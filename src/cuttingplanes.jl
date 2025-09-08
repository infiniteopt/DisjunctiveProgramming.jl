function reformulate_disjunction(model::JuMP.AbstractModel, disj::Disjunction, method::AbstractReformulationMethod)
    ref_cons = Vector{JuMP.AbstractConstraint}() #store reformulated constraints
    for d in disj.indicators
        _reformulate_disjunct(model, ref_cons, d, method)
    end
    return ref_cons
end

#I need to map variables between the different models


function _map_variables(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef, 
    method::cutting_planes
)

end


function _initialize_relaxed_bigM(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef, 
    method::cutting_planes
)
    rBM = copy(model)
    reformulate_disjunctions(rBM, BigM())


    #Get solution
    #Pass solution
    return ref_cons
end

function _initialize_relaxed_SEP(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef, 
    method::cutting_planes
)
    #Copy model (hull)
    #Set obj to Minimize distance
    #Solve
    #Get solution
    #Pass solution
    return ref_cons
end

function _update_relaxed_bigM(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef, 
    method::cutting_planes
)
    #Copy model (bigM)
    #Solve relaxed_bigM
    #Get solution
    #Pass solution
    return ref_cons
end

function _update_relaxed_SEP(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef, 
    method::cutting_planes
)
    #Copy model (bigM)
    #Solve relaxed_bigM
    #Get solution
    #Pass solution
    return ref_cons
end

function _relaxed_SEP(
    model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef, 
    method::cutting_planes
)
    #Copy model (hull)
    #Set obj to Minimize distance
    #Solve
    #Get solution
    #Pass solution
    return ref_cons
end

function _add_cut(
    main_model::JuMP.AbstractModel, 
    rBM_model::JuMP.AbstractModel, 
    SEP_model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef, 
    method::cutting_planes
)
    #Add cut to all three models
    return
end

function _check_cut_quality(
    main_model::JuMP.AbstractModel, 
    rBM_model::JuMP.AbstractModel, 
    SEP_model::JuMP.AbstractModel, 
    ref_cons::Vector{JuMP.AbstractConstraint}, 
    lvref::LogicalVariableRef, 
    method::cutting_planes
)
    #Check cut quality
    return
end