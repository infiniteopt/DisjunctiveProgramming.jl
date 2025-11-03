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

function test_remapping_functions()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y)
    @variable(model, z)
    
    var_map = Dict{VariableRef, VariableRef}(x => y, z => x)
    
    @test DP._remap_indicator_to_binary(x, var_map) == y
    @test DP._remap_indicator_to_binary(z, var_map) == x
    
    aff_expr = 2.0 * x + 3.0 * z + 5.0
    remapped_expr = DP._remap_indicator_to_binary(aff_expr, var_map)
    @test remapped_expr isa JuMP.GenericAffExpr
    @test remapped_expr.constant == 5.0
    @test remapped_expr.terms[y] == 2.0  # x remapped to y
    @test remapped_expr.terms[x] == 3.0  # z remapped to x
    @test !haskey(remapped_expr.terms, z)  # z shouldn't exist anymore
    
    model2 = GDPModel()
    @variable(model2, a[1:3])
    @variable(model2, Y[1:3], DP.Logical)
    
    con1 = @constraint(model2, a[1] ≤ 5, DP.Disjunct(Y[1]))
    con2 = @constraint(model2, a[2] ≥ 2, DP.Disjunct(Y[2]))
    con3 = @constraint(model2, a[3] == 4, DP.Disjunct(Y[3]))
    
    disj1 = DP.@disjunction(model2, Y[1:2])
    disj2 = DP.@disjunction(model2, Y[2:3])
    
    disj_con_map = Dict{DisjunctConstraintRef{Model}, DisjunctConstraintRef{Model}}(
        con1 => con2,
        con2 => con3
    )
    disj_map = Dict{DisjunctionRef{Model}, DisjunctionRef{Model}}()
    
    @test DP._remap_constraint_to_indicator(con1, disj_con_map, disj_map) == con2
    @test DP._remap_constraint_to_indicator(con2, disj_con_map, disj_map) == con3
    
    empty_disj_con_map = Dict{DisjunctConstraintRef{Model}, DisjunctConstraintRef{Model}}()
    disj_map2 = Dict{DisjunctionRef{Model}, DisjunctionRef{Model}}(
        disj1 => disj2
    )
    
    @test DP._remap_constraint_to_indicator(disj1, empty_disj_con_map, disj_map2) == disj2
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
    new_model1, ref_map1, lv_map1 = DP.copy_gdp_model(model)
    @test haskey(new_model1.ext, :GDP)
    @test length(lv_map1) == 2

    orig_num_vars = num_variables(model)
    orig_num_constrs = num_constraints(model; 
    count_variable_in_set_constraints = false
    )
    orig1_num_vars = num_variables(new_model1)
    orig1_num_constrs = num_constraints(new_model1; 
    count_variable_in_set_constraints = false
    )
    
    @variable(new_model, z >= 0)
    @constraint(new_model, z <= 100)
    
    @test num_variables(model) == orig_num_vars
    num_con_m = num_constraints(model; 
    count_variable_in_set_constraints = false)
    num_con_m1 = num_constraints(new_model1; 
    count_variable_in_set_constraints = false)
    @test num_con_m == orig_num_constrs
    @test num_con_m1 == orig1_num_constrs
    @test !haskey(object_dictionary(model), :z)
    
    @test num_variables(new_model1) == orig1_num_vars
    
    @test !haskey(object_dictionary(new_model1), :z)

    @test num_variables(new_model) == orig_num_vars + 1
    num_con_m2 = num_constraints(new_model; 
    count_variable_in_set_constraints = false)
    @test num_con_m2 == orig_num_constrs + 1
    

    orig_num_lvars = length(DP._logical_variables(model))
    orig_num_disj_cons = length(DP._disjunct_constraints(model))
    orig_num_disj = length(DP._disjunctions(model))
    orig1_num_lvars = length(DP._logical_variables(new_model1))
    orig1_num_disj_cons = length(DP._disjunct_constraints(new_model1))
    orig1_num_disj = length(DP._disjunctions(new_model1))
    
    @variable(new_model, W[1:2], DP.Logical)
    @constraint(new_model, z >= 5, DP.Disjunct(W[1]))
    @constraint(new_model, z <= 3, DP.Disjunct(W[2]))
    DP.@disjunction(new_model, W)
    
    @test length(DP._logical_variables(model)) == orig_num_lvars
    @test length(DP._disjunct_constraints(model)) == orig_num_disj_cons
    @test length(DP._disjunctions(model)) == orig_num_disj
    @test !haskey(object_dictionary(model), :W)
    
    @test length(DP._logical_variables(new_model1)) == orig1_num_lvars
    @test length(DP._disjunct_constraints(new_model1)) == orig1_num_disj_cons
    @test length(DP._disjunctions(new_model1)) == orig1_num_disj
    @test !haskey(object_dictionary(new_model1), :W)
    
    @test length(DP._logical_variables(new_model)) == orig_num_lvars + 2
    @test length(DP._disjunct_constraints(new_model)) == orig_num_disj_cons + 2
    @test length(DP._disjunctions(new_model)) == orig_num_disj + 1
end

@testset "GDP Model" begin
    test_GDPData()
    test_empty_model()
    test_non_gdp_model()
    test_copy_model()
    test_creation_optimizer()
    test_set_optimizer()
    test_remapping_functions()
end
