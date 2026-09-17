function test_macro_helpers()
    @test DP._esc_non_constant(1) == 1
    @test_throws ErrorException DP._error_if_cannot_register(error, Model(), 42)
end

function test_disjunction_add_fail()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2], Logical)
    @constraint(model, x == 5, Disjunct(y[1]))
    
    @test_macro_throws ErrorException @disjunction(model) #not enough arguments
    @test_macro_throws ErrorException @disjunction(42, y) #a model was not given
    @test_macro_throws ErrorException @disjunction(model, "bob"[i = 1:1], y[1:1]) #bad name
    @test_macro_throws UndefVarError @disjunction(model, y) #unassociated indicator
    @test_macro_throws UndefVarError @disjunction(GDPModel(), y) #wrong model
    @test_throws ErrorException disjunction(Model(), y) #not a GDPModel
    @test_macro_throws UndefVarError @disjunction(model, [y[1], y[1]]) #duplicate indicator
    @test_macro_throws UndefVarError @disjunction(model, y[1]) #unrecognized disjunction expression
    @test_throws ErrorException disjunction(model, y[1]) #unrecognized disjunction expression
    @test_throws ErrorException disjunction(model, [1]) #unrecognized disjunction expression
    @test_macro_throws UndefVarError @disjunction(model, y, "random_arg") #unrecognized extra argument
    @test_throws ErrorException DP._disjunction(error, model, y, "y", "random_arg") #unrecognized extra argument
    @test_macro_throws ErrorException @disjunction(model, "ABC") #unrecognized structure
    @test_macro_throws ErrorException @disjunction(model, begin y end) #@disjunctions (plural)
    @test_macro_throws UndefVarError @disjunction(model, x, y) #name x already exists

    @constraint(model, x == 10, Disjunct(y[2]))
    @disjunction(model, disj, y)
    @test model[:disj] isa DisjunctionRef
    @test_macro_throws UndefVarError @disjunction(model, disj, y) #duplicate name
    @test_throws ErrorException DP._error_if_cannot_register(error, model, :disj) #duplicate name

    @test_macro_throws ErrorException @disjunction(model, "bad"[i=1:2], y) #wrong expression for disjunction name
    @test_macro_throws ErrorException @disjunction(model, [model=1:2], y) #index name can't be same as model name

    @test_throws ErrorException disjunction(model, y, bad_key = 42)
    @variable(model, w[1:3], Logical)
    @constraint(model, [i = 1:2], x == 5, Disjunct(w[i]))
    @test_throws ErrorException disjunction(model, w, Disjunct(w[3]), bad_key = 42)

    @variable(model, yc[i = 1:2], Logical, logical_complement = y[i])
    @test_throws ErrorException disjunction(model, [yc[1]])
    @test_throws ErrorException disjunction(model, [yc[1], y[2]])
    @test_throws ErrorException disjunction(model, [y[1], yc[1]], Disjunct(y[2]))

    other_model = GDPModel()
    @variable(other_model, v[1:2], Logical)
    @test_throws ErrorException disjunction(model, [y[1], v[1]]) #indicator from another model
end

function test_disjunction_add_success()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2], Logical)
    @constraint(model, x == 5, Disjunct(y[1]))
    @constraint(model, x == 10, Disjunct(y[2]))
    disj = DisjunctionRef(model, DisjunctionIndex(1))
    disj2 = DisjunctionRef(model, DisjunctionIndex(2))
    @test @disjunction(model, y) == disj
    @test @disjunction(model, disj2, y, exactly1 = false) == disj2
    @test owner_model(disj) == model
    @test is_valid(model, disj)
    @test index(disj) == DisjunctionIndex(1)
    @test name(disj) == ""
    @test name(disj2) == "disj2"
    @test haskey(DP._disjunctions(model), index(disj))
    @test haskey(DP._disjunctions(model), index(disj2))
    @test DP._disjunctions(model)[index(disj)] == DP._constraint_data(disj)
    @test !constraint_object(disj).nested
    @test constraint_object(disj).indicators == y
    @test haskey(gdp_data(model).exactly1_constraints, disj)
    @test !haskey(gdp_data(model).exactly1_constraints, disj2)
    @test disj == copy(disj)
end

function test_disjunction_add_nested()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2], Logical)
    @variable(model, z[1:2], Logical)
    @constraint(model, x <= 5, Disjunct(y[1]))
    @constraint(model, x >= 5, Disjunct(y[2]))
    inner = DisjunctionRef(model, DisjunctionIndex(1))
    @test @disjunction(model, inner, y, Disjunct(z[1])) == inner
    @constraint(model, x <= 10, Disjunct(z[1]))
    @constraint(model, x >= 10, Disjunct(z[2]))
    outer = DisjunctionRef(model, DisjunctionIndex(2))
    @test @disjunction(model, outer, z) == outer

    @test is_valid(model, inner)
    @test is_valid(model, outer)
    @test haskey(DP._disjunctions(model), index(inner))
    @test haskey(DP._disjunctions(model), index(outer))
    @test constraint_object(inner).nested
    @test !constraint_object(outer).nested
    @test haskey(DP._indicator_to_constraints(model), z[1])
    @test inner in DP._indicator_to_constraints(model)[z[1]]
    @test haskey(gdp_data(model).exactly1_constraints, inner)
end

function test_disjunction_add_array()
    model=GDPModel()
    @variable(model, x)
    @variable(model, y[1:2, 1:3, 1:4], Logical)
    @constraint(model, con[i=1:2, j=1:3, k=1:4], x==i+j+k, Disjunct(y[i,j,k]))
    @disjunction(model, disj[i=1:2, j=1:3], y[i,j,:]; container = Array)

    @test length(disj) == 6
    @test all(is_valid.(model, disj))
end

function test_disjunciton_add_dense_axis()
    model = GDPModel()
    @variable(model, x)
    I = ["a", "b", "c"]
    J = [1, 2]
    @variable(model, y[I, J, 1:4], Logical)
    @constraint(model, con[i=I, j=J, k=1:4], x==k, Disjunct(y[i,j,k]))
    @disjunction(model, disj[i=I, j=J], y[i,j,:])

    @test disj.axes[1] == ["a","b","c"]
    @test disj.axes[2] == [1,2]
    @test disj.data isa Matrix{DisjunctionRef{Model}}
end

function test_disjunction_add_sparse_axis()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:3, 1:3, 1:4], Logical)
    @constraint(model, con[i=1:3, j=1:3, k=1:4; j > i], x==i+j+k, Disjunct(y[i,j,k]))
    @disjunction(model, disj[i=1:3, j=1:3; j > i], y[i,j,:])

    @test length(disj) == 3
    @test disj.names == (:i, :j)
    @test Set(keys(disj.data)) == Set([(1,2),(1,3),(2,3)])
end

function test_disjunctions_add_fail()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2], Logical)
    @variable(model, z[1:2], Logical)
    @constraint(model, x <= 5, Disjunct(y[1]))
    @constraint(model, x >= 5, Disjunct(y[2]))
    @test_macro_throws ErrorException @disjunctions(model, y)
end

function test_disjunctions_add_success()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2], Logical)
    @variable(model, z[1:2], Logical)
    @constraint(model, x <= 5, Disjunct(y[1]))
    @constraint(model, x >= 5, Disjunct(y[2]))
    @constraint(model, x <= 10, Disjunct(z[1]))
    @constraint(model, x >= 10, Disjunct(z[2]))
    @disjunctions(model, begin
        disj1, y, (base_name = "bob", container = Array)
        disj2, z
    end)
    @test is_valid(model, disj1)
    @test is_valid(model, disj2)
    @test haskey(DP._disjunctions(model), index(disj1))
    @test haskey(DP._disjunctions(model), index(disj2))
    @test name(disj1) == "bob"

    unamed = @disjunctions(model, begin
        y
        z
    end)
    @test all(is_valid.(model, unamed))
    @test haskey(DP._disjunctions(model), index(unamed[1]))
    @test haskey(DP._disjunctions(model), index(unamed[2]))
end

function test_disjunction_set_name()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2], Logical)
    @constraint(model, x == 5, Disjunct(y[1]))
    @constraint(model, x == 10, Disjunct(y[2]))
    @disjunction(model, disj, y)
    set_name(disj, "new_name")
    @test name(disj) == "new_name"
end

function test_disjunction_delete()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2], Logical)
    @constraint(model, x == 5, Disjunct(y[1]))
    @constraint(model, x == 10, Disjunct(y[2]))
    @disjunction(model, disj, y)

    @test_throws AssertionError delete(GDPModel(), disj)
    @test delete(model, disj) isa Nothing
    @test !haskey(gdp_data(model).disjunctions, index(disj))
    @test !DP._ready_to_optimize(model)
    @test !haskey(gdp_data(model).exactly1_constraints, disj)

    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2], Logical)
    @variable(model, z[1:2], Logical)
    @constraint(model, x <= 5, Disjunct(y[1]))
    @constraint(model, x >= 5, Disjunct(y[2]))
    @disjunction(model, inner, y, Disjunct(z[1]), exactly1 = false)

    @test delete(model, inner) isa Nothing
    @test !haskey(gdp_data(model).disjunctions, index(inner))
    @test !haskey(gdp_data(model).constraint_to_indicator, disj)
    @test !(inner in gdp_data(model).indicator_to_constraints[z[1]])
end

function test_disjunction_function()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2], Logical)
    @constraint(model, x == 5, Disjunct(y[1]))
    @constraint(model, x == 10, Disjunct(y[2]))
    disj = DisjunctionRef(model, DisjunctionIndex(1))
    @test disjunction(model, y, "name") == disj

    @test is_valid(model, disj)
    @test name(disj) == "name"
    set_name(disj, "new_name")
    @test name(disj) == "new_name"
    @test haskey(DP._disjunctions(model), index(disj))
    @test haskey(gdp_data(model).exactly1_constraints, disj)
end

function test_disjunction_function_nested()
    model = GDPModel()
    @variable(model, x)
    @variable(model, y[1:2], Logical)
    @variable(model, z[1:2], Logical)
    @constraint(model, x <= 5, Disjunct(y[1]))
    @constraint(model, x >= 5, Disjunct(y[2]))
    @constraint(model, x <= 10, Disjunct(z[1]))
    @constraint(model, x >= 10, Disjunct(z[2]))
    disj1 = DisjunctionRef(model, DisjunctionIndex(1))
    disj2 = DisjunctionRef(model, DisjunctionIndex(2))
    @test disjunction(model, y, Disjunct(z[1]), "inner", exactly1 = false) == disj1
    @test disjunction(model, z, "outer") == disj2

    @test is_valid(model, disj1)
    @test is_valid(model, disj2)
    @test haskey(DP._disjunctions(model), index(disj1))
    @test haskey(DP._disjunctions(model), index(disj2))
    @test constraint_object(disj1).nested
    @test !constraint_object(disj2).nested
    @test haskey(DP._indicator_to_constraints(model), z[1])
    @test disj1 in DP._indicator_to_constraints(model)[z[1]]
    @test !haskey(gdp_data(model).exactly1_constraints, disj1)
end

function test_extension_disjunctions()
    model = GDPModel{MyModel, MyVarRef, MyConRef}()
    @variable(model, y[1:2], Logical(MyVar), start = true)
    @variable(model, 0 <= x[1:2] <= 1)
    crefs = [DisjunctConstraintRef(model, DisjunctConstraintIndex(i)) for i in 1:2]
    @test @constraint(model, [i = 1:2], x[i]^2 >= 0.5, Disjunct(y[i])) == crefs
    dref = DisjunctionRef(model, DisjunctionIndex(1))
    @test @disjunction(model, y, base_name = "test") == dref
    @test name(dref) == "test"
    dref2 = DisjunctionRef(model, DisjunctionIndex(2))
    @test disjunction(model, y) == dref2
    @test length(DP._disjunctions(model)) == 2
    @test length(DP._disjunct_constraints(model)) == 2
    @test delete(model, dref2) isa Nothing
    @test !is_valid(model, dref2)
end

@testset "Disjunction" begin
    @testset "Macro Helpers" begin
        test_macro_helpers()
    end
    @testset "Add Disjunction" begin
        test_disjunction_add_fail()
        test_disjunction_add_success()
        test_disjunction_add_nested()
        test_disjunction_add_array()
        test_disjunciton_add_dense_axis()
        test_disjunction_add_sparse_axis()
        test_disjunctions_add_fail()
        test_disjunctions_add_success()
        test_disjunction_function()
        test_disjunction_function_nested()
    end
    @testset "Disjunction Properties" begin
        test_disjunction_set_name()
    end
    @testset "Delete Disjunction" begin
        test_disjunction_delete()
    end
    @testset "Test Extension" begin
        test_extension_disjunctions()
    end
end