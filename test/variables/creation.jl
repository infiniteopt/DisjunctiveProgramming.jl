function test_VariableProperties()
    model = Model()
    @variable(model, x >= 1, start = 2.5)
    @variable(model, y <= 10)
    @variable(model, z == 5)
    @variable(model, w, Bin)
    @variable(model, v, Int)
    @variable(model, u)

    x_props = DP.VariableProperties(x)
    y_props = DP.VariableProperties(y)
    z_props = DP.VariableProperties(z)
    w_props = DP.VariableProperties(w)
    v_props = DP.VariableProperties(v)
    u_props = DP.VariableProperties(u)

    @test x_props.is_fixed == false
    @test x_props.is_binary == false
    @test x_props.is_integer == false
    @test x_props.lower_bound == 1
    @test x_props.upper_bound === nothing
    @test x_props.fix_value === nothing
    @test x_props.start_value == 2.5

    @test y_props.lower_bound === nothing
    @test y_props.upper_bound == 10

    @test z_props.is_fixed == true
    @test z_props.fix_value == 5

    @test w_props.is_binary == true
    @test v_props.is_integer == true

    @test u_props.lower_bound === nothing
    @test u_props.upper_bound === nothing
end

function test_variable_from_properties()
    model = Model()
    props = DP.VariableProperties()
    props.name = "x"
    props.is_binary = false
    props.is_integer = false
    props.lower_bound = 0.0
    props.upper_bound = 10.0
    props.fix_value = nothing
    props.start_value = 2.5
    var = DP._variable_from_properties(model, props)

    @test JuMP.name(var) == "x"
    @test JuMP.lower_bound(var) == 0.0
    @test JuMP.upper_bound(var) == 10.0
    @test JuMP.is_fixed(var) == false
    @test JuMP.is_binary(var) == false
    @test JuMP.is_integer(var) == false
    @test JuMP.has_start_value(var) == true
    @test JuMP.start_value(var) == 2.5
end

@testset "Variable Creation" begin
    test_VariableProperties()
    test_variable_from_properties()
end