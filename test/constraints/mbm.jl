#Testing replacement of variables
#TODO: Test bad inputs throw errors for MINI MODEL
#TODO: Test MBM datatype 
using Gurobi
using Revise
function test_replace_variables_in_constraint()
    model = Model()
    sub_model = Model()
    @variable(model, x[1:3])
    @constraint(model, con1,x[1] <= 1)
    @constraint(model, con2,x[2]*x[1] <= 1)
    @constraint(model, con3,sin(x[3]) <= 0)
    @constraint(model, con4, [x[1],x[2],x[3]] in MOI.Zeros(3))
    
    #Test GenericVariableRef
    new_vars = Dict{VariableRef, VariableRef}()
    [new_vars[x[i]] = @variable(sub_model) for i in 1:3]
    varref = DP.replace_variables_in_constraint(x[1], new_vars)
    expr1 = DP.replace_variables_in_constraint(constraint_object(con1).func, new_vars)
    expr2 = DP.replace_variables_in_constraint(constraint_object(con2).func, new_vars)
    expr3 = DP.replace_variables_in_constraint(constraint_object(con3).func, new_vars)
    expr4 = DP.replace_variables_in_constraint(constraint_object(con4).func, new_vars)
    @test expr1 == JuMP.@expression(sub_model, new_vars[x[1]] + 1 - 1)
    @test expr2 == JuMP.@expression(sub_model, new_vars[x[2]]*new_vars[x[1]])
    @test varref == new_vars[x[1]]
    # Test nonlinear expression structure
    #TODO: Fix expr3 test, for some reason it's not as easy to compare
    @test expr3 isa JuMP.NonlinearExpr  # Test it's a nonlinear expression
    @test expr4 == [new_vars[x[i]] for i in 1:3]
    @test_throws ErrorException DP.replace_variables_in_constraint("String", new_vars)
end

function test_constraint_to_objective()
    model = Model()
    sub_model = Model()

    @variable(model, x[1:2])
    @constraint(model, lessthan, x[1] <= 1) 
    @constraint(model, greaterthan, x[2] >= 1)
    @constraint(model, interval, 0 <= x[1] <= 55)
    @constraint(model, equalto, x[1] == 1)
    new_vars = Dict{VariableRef, VariableRef}()
    [new_vars[x[i]] = @variable(sub_model) for i in 1:2]
    DP.constraint_to_objective(sub_model, constraint_object(lessthan), new_vars)
    @test objective_function(sub_model) == JuMP.@expression(sub_model, new_vars[x[1]] - 1)
    DP.constraint_to_objective(sub_model, constraint_object(greaterthan), new_vars)
    @test objective_function(sub_model) == JuMP.@expression(sub_model, 1 - new_vars[x[2]])
    @test_throws ErrorException DP.constraint_to_objective(sub_model, constraint_object(interval), new_vars)
end

function test_maximize_M()
    model = GDPModel()
    @variable(model, 0 <= x[1:2] <= 50)
    @variable(model, Y[1:6], Logical)
    @constraint(model, lessthan, x[1] <= 1, Disjunct(Y[1]))
    @constraint(model, greaterthan, x[1] >= 1, Disjunct(Y[1]))
    @constraint(model, interval, 0 <= x[1] <= 55, Disjunct(Y[2]))
    @constraint(model, equalto, x[1] == 1, Disjunct(Y[3]))
    @constraint(model, nonpositives, -x in MOI.Nonpositives(2), Disjunct(Y[4]))
    @constraint(model, nonnegatives, x in MOI.Nonnegatives(2), Disjunct(Y[5]))
    @constraint(model, zeros, -x .+ 1 in MOI.Zeros(2), Disjunct(Y[6]))
    @test DP._maximize_M(model, constraint_object(lessthan), Vector{DisjunctConstraintRef}(DP._indicator_to_constraints(model)[Y[2]]), MBM(Gurobi.Optimizer)) == 49
    @test DP._maximize_M(model, constraint_object(greaterthan), Vector{DisjunctConstraintRef}(DP._indicator_to_constraints(model)[Y[2]]), MBM(Gurobi.Optimizer)) == 1.0
    @test DP._maximize_M(model, constraint_object(interval), Vector{DisjunctConstraintRef}(DP._indicator_to_constraints(model)[Y[1]]), MBM(Gurobi.Optimizer)) == -1.0
    @test DP._maximize_M(model, constraint_object(equalto), Vector{DisjunctConstraintRef}(DP._indicator_to_constraints(model)[Y[3]]), MBM(Gurobi.Optimizer)) == 0
    @test DP._maximize_M(model, constraint_object(nonpositives), Vector{DisjunctConstraintRef}(DP._indicator_to_constraints(model)[Y[2]]), MBM(Gurobi.Optimizer)) == 0
    @test DP._maximize_M(model, constraint_object(nonnegatives), Vector{DisjunctConstraintRef}(DP._indicator_to_constraints(model)[Y[2]]), MBM(Gurobi.Optimizer)) == 0
    @test DP._maximize_M(model, constraint_object(zeros), Vector{DisjunctConstraintRef}(DP._indicator_to_constraints(model)[Y[2]]), MBM(Gurobi.Optimizer)) == 49
    @test_throws ErrorException DP._maximize_M(model, "odd", Vector{DisjunctConstraintRef}(DP._indicator_to_constraints(model)[Y[2]]), MBM(Gurobi.Optimizer))
end

function test_reformulate_disjunct_constraint()
    model = GDPModel()
    @variable(model, 0 <= x[1:2] <= 50)
    @variable(model, Y[1:6], Logical)
    @constraint(model, lessthan, x[1] <= 1, Disjunct(Y[1]))
    @constraint(model, greaterthan, x[1] >= 1, Disjunct(Y[1]))
    @constraint(model, interval, 0 <= x[1] <= 55, Disjunct(Y[2]))
    @constraint(model, equalto, x[1] == 1, Disjunct(Y[3]))
    @constraint(model, nonpositives, -x in MOI.Nonpositives(2), Disjunct(Y[4]))
    @constraint(model, nonnegatives, x in MOI.Nonnegatives(2), Disjunct(Y[5]))
    @constraint(model, zeros, -x .+ 1 in MOI.Zeros(2), Disjunct(Y[6]))

    M = Float64[1,2,3,4,5,6]
    bconref = [binary_variable(Y[i]) for i in 1:6]
    reformulated_constraints = [reformulate_disjunct_constraint(model, constraint_object(constraints), bconref, M, MBM(Gurobi.Optimizer)) for constraints in [lessthan, greaterthan, interval, equalto, nonpositives, nonnegatives, zeros]]
    @test reformulated_constraints[1][1].func == JuMP.@expression(model, x[1] - sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_constraints[1][1].set == MOI.LessThan(1.0)
    @test reformulated_constraints[2][1].func == JuMP.@expression(model, x[1] + sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_constraints[2][1].set == MOI.GreaterThan(1.0)
    @test reformulated_constraints[3][2].func == JuMP.@expression(model, x[1] + sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_constraints[3][1].set == MOI.GreaterThan(0.0)
    @test reformulated_constraints[3][1].func == JuMP.@expression(model, x[1] - sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_constraints[3][2].set == MOI.LessThan(55.0)
    @test reformulated_constraints[4][1].func == JuMP.@expression(model, x[1] + sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_constraints[4][1].set == MOI.GreaterThan(1.0)
    @test reformulated_constraints[4][2].func == JuMP.@expression(model, x[1] - sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_constraints[4][2].set == MOI.LessThan(1.0)
    @test reformulated_constraints[5][1].func == JuMP.@expression(model, -x .- sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_constraints[5][1].set == MOI.Nonpositives(2)
    @test reformulated_constraints[6][1].func == JuMP.@expression(model, x .+ sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_constraints[6][1].set == MOI.Nonnegatives(2)
    @test reformulated_constraints[7][1].func == JuMP.@expression(model, -x .+(1 + sum(M[i] * bconref[i] for i in 1:length(M)))) && reformulated_constraints[7][1].set == MOI.Nonnegatives(2)
    @test reformulated_constraints[7][2].func == JuMP.@expression(model, -x .+(1 - sum(M[i] * bconref[i] for i in 1:length(M)))) && reformulated_constraints[7][2].set == MOI.Nonpositives(2)
end

function test_reformulate_disjunct()
    model = GDPModel()
    @variable(model, 1 <= x[1:2] <= 50)
    @variable(model, Y[1:6], Logical)
    @constraint(model, lessthan, x[1] <= 2, Disjunct(Y[1]))
    @constraint(model, greaterthan, x[1] >= 1, Disjunct(Y[1]))
    @constraint(model, interval, 0 <= x[1] <= 55, Disjunct(Y[2]))
    @constraint(model, equalto, x[1] == 1, Disjunct(Y[3]))
    @constraint(model, nonpositives, -x in MOI.Nonpositives(2), Disjunct(Y[4]))
    @constraint(model, nonnegatives, x in MOI.Nonnegatives(2), Disjunct(Y[5]))
    @constraint(model, zeros, -x .+ 1 in MOI.Zeros(2), Disjunct(Y[6]))
    @disjunction(model, [Y[1], Y[2], Y[3], Y[4], Y[5], Y[6]])

    reformulated_disjunct = DP._reformulate_disjunct(model,Vector{JuMP.AbstractConstraint}(),Y[1], LogicalVariableRef[Y[2], Y[3], Y[4], Y[5], Y[6]], MBM(Gurobi.Optimizer))
    M = [48.0, -0.0, 48.0, 48.0, -0.0]
    bconref = [binary_variable(Y[i]) for i in 2:6]
    @test reformulated_disjunct[1].func == JuMP.@expression(model, x[1] - sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_disjunct[1].set == MOI.LessThan(2.0)
    @test reformulated_disjunct[2].func == JuMP.@expression(model, x[1] + sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_disjunct[2].set == MOI.GreaterThan(1.0)

    reformulated_disjunct = DP._reformulate_disjunct(model,Vector{JuMP.AbstractConstraint}(),Y[2], LogicalVariableRef[Y[1], Y[3], Y[4], Y[5], Y[6]], MBM(Gurobi.Optimizer))
    M = [1.0, 0.0, 1.0, 1.0, 1.0, 1.0]
    bconref = [binary_variable(Y[i]) for i in 1:6]
    @test reformulated_disjunct[2].func == JuMP.@expression(model, x[1] - sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_disjunct[2].set == MOI.LessThan(55.0)
    @test reformulated_disjunct[1].func == JuMP.@expression(model, x[1] + sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_disjunct[1].set == MOI.GreaterThan(0.0)

    reformulated_disjunct = DP._reformulate_disjunct(model,Vector{JuMP.AbstractConstraint}(),Y[3], LogicalVariableRef[Y[1], Y[2], Y[4], Y[5], Y[6]], MBM(Gurobi.Optimizer))
    M = [1.0, 49.0, 0.0, 49.0, 49.0, 0.0]
    bconref = [binary_variable(Y[i]) for i in 1:6]
    @test reformulated_disjunct[2].func == JuMP.@expression(model, x[1] - sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_disjunct[2].set == MOI.LessThan(1.0)
    @test reformulated_disjunct[1].func == JuMP.@expression(model, x[1] + sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_disjunct[1].set == MOI.GreaterThan(1.0)

    reformulated_disjunct = DP._reformulate_disjunct(model,Vector{JuMP.AbstractConstraint}(),Y[4], LogicalVariableRef[Y[1], Y[2], Y[3], Y[5], Y[6]], MBM(Gurobi.Optimizer))
    M = [-1.0, -1.0, -1.0, 0.0, -1.0, -1.0]
    bconref = [binary_variable(Y[i]) for i in 1:6]
    @test reformulated_disjunct[1].func == JuMP.@expression(model, -x .- sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_disjunct[1].set == MOI.Nonpositives(2)
    
    reformulated_disjunct = DP._reformulate_disjunct(model,Vector{JuMP.AbstractConstraint}(),Y[5], LogicalVariableRef[Y[1], Y[2], Y[3], Y[4], Y[6]], MBM(Gurobi.Optimizer))
    M = [-1.0, -1.0, -1.0, -1.0, 0.0, -1.0]
    bconref = [binary_variable(Y[i]) for i in 1:6]
    @test reformulated_disjunct[1].func == JuMP.@expression(model, x .+ sum(M[i] * bconref[i] for i in 1:length(M))) && reformulated_disjunct[1].set == MOI.Nonnegatives(2)
    
    reformulated_disjunct = DP._reformulate_disjunct(model,Vector{JuMP.AbstractConstraint}(),Y[6], LogicalVariableRef[Y[1], Y[2], Y[3], Y[4], Y[5]], MBM(Gurobi.Optimizer))
    M = [49.0, 49.0, 49.0, 49.0, 49.0, 0.0]
    bconref = [binary_variable(Y[i]) for i in 1:6]
    println(reformulated_disjunct)
    @test reformulated_disjunct[1].func == JuMP.@expression(model, -x .+ sum(M[i] * bconref[i] for i in 1:length(M)) .+ 1) && reformulated_disjunct[1].set == MOI.Nonnegatives(2)
    @test reformulated_disjunct[2].func == JuMP.@expression(model, -x .- sum(M[i] * bconref[i] for i in 1:length(M)) .+ 1) && reformulated_disjunct[2].set == MOI.Nonpositives(2)
end

@testset "MBM" begin
    # test_replace_variables_in_constraint()
    # test_constraint_to_objective()
    # test_maximize_M()
    # test_reformulate_disjunct_constraint()
    test_reformulate_disjunct()
end


