function test_VariableProperties_constructor()
    model = Model()
    
    @variable(model, x, lower_bound = 2.5)
    x_props = DP.VariableProperties(x)
    @test x_props.info.has_lb == true
    @test x_props.info.lower_bound == 2.5
    @test x_props.info.has_ub == false
    @test x_props.info.upper_bound == 0.0
    @test x_props.info.has_fix == false
    @test x_props.info.fixed_value == 0.0
    @test x_props.info.has_start == false
    @test x_props.name == "x"
    @test x_props.set === nothing
    @test x_props.variable_type === nothing
    
    @variable(model, y, start = 3.14)
    y_props = DP.VariableProperties(y)
    @test y_props.info.has_start == true
    @test y_props.info.start == 3.14
    @test y_props.info.has_lb == false
    @test y_props.info.lower_bound == 0.0
    
    @variable(model, z == 7.5)
    z_props = DP.VariableProperties(z)
    @test z_props.info.has_fix == true
    @test z_props.info.fixed_value == 7.5
    @test z_props.info.has_lb == false
    @test z_props.info.lower_bound == 0.0
end

function test_make_variable_object()
    model = Model()
    
    @variable(model, x, lower_bound = 1.0, upper_bound = 5.0)
    props = DP.VariableProperties(x)

    modified_info = JuMP.VariableInfo(
        props.info.has_lb,
        props.info.lower_bound,
        props.info.has_ub,
        10.0,  # Modified upper bound
        props.info.has_fix,
        props.info.fixed_value,
        props.info.has_start,
        props.info.start,
        props.info.binary,
        props.info.integer
    )

    props.info = modified_info
    
    var_obj = DP._make_variable_object(props)
    @test var_obj.info.upper_bound == 10.0
end

function test_create_variable()
    model1 = Model()
    model2 = Model()
    
    @variable(model1, x, lower_bound = 1.0, upper_bound = 5.0, start = 2.0)
    props_no_set = DP.VariableProperties(x)
    
    @test props_no_set.set === nothing
    
    var_no_set = DP.create_variable(model2, props_no_set)
    
    @test var_no_set !== nothing
    @test JuMP.name(var_no_set) == "x"
    @test JuMP.has_lower_bound(var_no_set) == true
    @test JuMP.lower_bound(var_no_set) == 1.0
    @test JuMP.has_upper_bound(var_no_set) == true  
    @test JuMP.upper_bound(var_no_set) == 5.0
    @test JuMP.has_start_value(var_no_set) == true
    @test JuMP.start_value(var_no_set) == 2.0
    
    @test var_no_set in JuMP.all_variables(model2)
    @test !(var_no_set in JuMP.all_variables(model1))
end

function test_complete_workflow()
    model1 = Model()
    model2 = Model()
    
    @variable(model1, original, lower_bound = 1, upper_bound = 5, start = 3.0)
    
    props = DP.VariableProperties(original)
    
    recreated = DP.create_variable(model2, props)
    
    @test JuMP.has_lower_bound(recreated) == JuMP.has_lower_bound(original)
    @test JuMP.lower_bound(recreated) == JuMP.lower_bound(original)
    @test JuMP.has_upper_bound(recreated) == JuMP.has_upper_bound(original)
    @test JuMP.upper_bound(recreated) == JuMP.upper_bound(original)
    @test JuMP.has_start_value(recreated) == JuMP.has_start_value(original)
    @test JuMP.start_value(recreated) == JuMP.start_value(original)
    @test JuMP.name(recreated) == JuMP.name(original)
    
    @test original in JuMP.all_variables(model1)
    @test recreated in JuMP.all_variables(model2)
    @test !(original in JuMP.all_variables(model2))
    @test !(recreated in JuMP.all_variables(model1))
end

function test_variable_copy()
    model1 = Model()
    model2 = Model()
    
    @variable(model1, original, lower_bound = 1, upper_bound = 5, start = 3.0)
    
    props = DP.VariableProperties(original)
    
    recreated = DP.create_variable(model2, props)
    
    @test JuMP.has_lower_bound(recreated) == JuMP.has_lower_bound(original)
    @test JuMP.lower_bound(recreated) == JuMP.lower_bound(original)
    @test JuMP.has_upper_bound(recreated) == JuMP.has_upper_bound(original)
    @test JuMP.upper_bound(recreated) == JuMP.upper_bound(original)
    @test JuMP.has_start_value(recreated) == JuMP.has_start_value(original)
    @test JuMP.start_value(recreated) == JuMP.start_value(original)
    @test JuMP.name(recreated) == JuMP.name(original)
    println("##################################")
    @test original in JuMP.all_variables(model1)
    @test recreated in JuMP.all_variables(model2)
    @test !(original in JuMP.all_variables(model2))
    @test !(recreated in JuMP.all_variables(model1))
end

@testset "Variable Creation" begin
    test_VariableProperties_constructor()
    test_make_variable_object()
    test_create_variable()
    test_complete_workflow()
end