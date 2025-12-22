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
    
    # Test variable_copy function directly
    copied = DP.variable_copy(model2, original)
    
    @test JuMP.has_lower_bound(copied) == JuMP.has_lower_bound(original)
    @test JuMP.lower_bound(copied) == JuMP.lower_bound(original)
    @test JuMP.has_upper_bound(copied) == JuMP.has_upper_bound(original)
    @test JuMP.upper_bound(copied) == JuMP.upper_bound(original)
    @test JuMP.has_start_value(copied) == JuMP.has_start_value(original)
    @test JuMP.start_value(copied) == JuMP.start_value(original)
    @test JuMP.name(copied) == JuMP.name(original)

    @test original in JuMP.all_variables(model1)
    @test copied in JuMP.all_variables(model2)
    @test !(original in JuMP.all_variables(model2))
    @test !(copied in JuMP.all_variables(model1))
end

function test_get_variable_info()
    model = Model()
    
    # Test with all properties set
    @variable(model, x, lower_bound = 1.0, upper_bound = 10.0, start = 5.0)
    info = DP.get_variable_info(x)
    @test info.has_lb == true
    @test info.lower_bound == 1.0
    @test info.has_ub == true
    @test info.upper_bound == 10.0
    @test info.has_start == true
    @test info.start == 5.0
    @test info.has_fix == false
    @test info.binary == false
    @test info.integer == false
    
    # Test with binary variable
    @variable(model, y, Bin)
    info_bin = DP.get_variable_info(y)
    @test info_bin.binary == true
    @test info_bin.integer == false
    
    # Test with integer variable
    @variable(model, z, Int)
    info_int = DP.get_variable_info(z)
    @test info_int.binary == false
    @test info_int.integer == true
    
    # Test with fixed variable
    @variable(model, w == 7.5)
    info_fix = DP.get_variable_info(w)
    @test info_fix.has_fix == true
    @test info_fix.fixed_value == 7.5
    
    # Test with overridden parameters
    info_override = DP.get_variable_info(x, has_lb = false, upper_bound = 20.0)
    @test info_override.has_lb == false
    @test info_override.lower_bound == 0  # Default when has_lb is false
    @test info_override.upper_bound == 20.0  # Overridden
end

function test_variable_properties_from_expr()
    model = Model()
    
    # Test with expression (for extensions - base ignores it)
    @variable(model, x)
    expr = 2*x + 1
    props = DP.VariableProperties(expr)
    @test props.name == ""
    @test props.info.has_lb == false
    @test props.info.has_ub == false
    var = DP.create_variable(model, props)
    JuMP.set_name(var, "from_expr")
    @test JuMP.name(var) == "from_expr"
    @test JuMP.has_lower_bound(var) == false
    @test JuMP.has_upper_bound(var) == false
    @test JuMP.is_fixed(var) == false
    @test JuMP.is_binary(var) == false
    @test JuMP.is_integer(var) == false
    @test var in JuMP.all_variables(model)
end

function test_create_variable_with_set()
    model = Model()
    
    info = DP._free_variable_info()
    props = DP.VariableProperties(info, "test_var", MOI.ZeroOne(), nothing)
    
    @test props.set !== nothing
    
    var = DP.create_variable(model, props)
    
    @test var !== nothing
    @test JuMP.name(var) == "test_var"
    @test var in JuMP.all_variables(model)
end

@testset "Variable Creation" begin
    test_VariableProperties_constructor()
    test_make_variable_object()
    test_create_variable()
    test_create_variable_with_set()
    test_complete_workflow()
    test_variable_copy()
    test_get_variable_info()
    test_variable_properties_from_expr()
end