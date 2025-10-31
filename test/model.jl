using HiGHS

function test_GDPData()
    @test GDPData{Model, VariableRef, ConstraintRef}() isa GDPData{Model, VariableRef, ConstraintRef, Float64}
end

function test_empty_model()
    @test GDPModel{GenericModel{Float16}, GenericVariableRef{Float16}, ConstraintRef}() isa GenericModel{Float16}
    @test GDPModel{Int}() isa GenericModel{Int}
    @test GDPModel{MyModel, MyVarRef, MyConRef}() isa MyModel
    model = GDPModel()
    @test gdp_data(model) isa GDPData
    @test isempty(DP._logical_variables(model))
    @test isempty(DP._logical_constraints(model))
    @test isempty(DP._disjunct_constraints(model))
    @test isempty(DP._disjunctions(model))
    @test isempty(DP._exactly1_constraints(model))
    @test isempty(DP._indicator_to_binary(model))
    @test isempty(DP._indicator_to_constraints(model))
    @test isempty(DP._constraint_to_indicator(model))
    @test isempty(DP._reformulation_variables(model))
    @test isempty(DP._reformulation_constraints(model))
    @test isempty(DP._variable_bounds(model))
    @test isnothing(DP._solution_method(model))
    @test !DP._ready_to_optimize(model)
end

function test_non_gdp_model()
    model = Model()
    @test_throws ErrorException gdp_data(model)
end

function test_creation_optimizer()
    model = GDPModel(HiGHS.Optimizer)
    @test solver_name(model) == "HiGHS"
end

function test_set_optimizer()
    model = GDPModel()
    set_optimizer(model, HiGHS.Optimizer)
    @test solver_name(model) == "HiGHS"
end

function test_copy_model()
    model = DP.GDPModel(HiGHS.Optimizer)
    @variable(model, 0 ≤ x[1:2] ≤ 20)
    @variable(model, Y[1:2], DP.Logical)
    @constraint(model, [i = 1:2], [2,5][i] ≤ x[i] ≤ [6,9][i], DP.Disjunct(Y[1]))
    @constraint(model, [i = 1:2], [8,10][i] ≤ x[i] ≤ [11,15][i], DP.Disjunct(Y[2]))
    DP.@disjunction(model, Y)
    DP._variable_bounds(model)[x[1]] = set_variable_bound_info(x[1], BigM())
    DP._variable_bounds(model)[x[2]] = set_variable_bound_info(x[2], BigM())
    
    new_model, ref_map = JuMP.copy_model(model)
    @test haskey(new_model.ext, :GDP)
    lv_map = DP.copy_gdp_data(model, new_model, ref_map)
    @test length(lv_map) == 2 
end

@testset "GDP Model" begin
    test_GDPData()
    test_empty_model()
    test_non_gdp_model()
    test_copy_model()
    test_creation_optimizer()
    test_set_optimizer()
end