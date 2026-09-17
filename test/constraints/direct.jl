function test_set_construction()
    set = DisjunctionSet([
        [MOI.LessThan(1.0), MOI.GreaterThan(0.0)],
        [MOI.EqualTo(2.0)],
    ])
    @test num_disjuncts(set) == 2
    @test MOI.dimension(set) == 1 + 2 + 3
    @test activation_index(set) == 1
    @test indicator_indices(set) == 2:3
    @test row_indices(set, 1) == 4:5
    @test row_indices(set, 2) == 6:6
    copied = copy(set)
    @test copied == set
    @test copied.inner_sets !== set.inner_sets
end

function test_set_interval_inner()
    set = DisjunctionSet([[MOI.Interval(0.0, 1.0)], [MOI.LessThan(0.0)]])
    @test MOI.dimension(set) == 5
end

function test_set_empty_disjunct()
    set = DisjunctionSet([
        MOI.AbstractScalarSet[],
        [MOI.LessThan(0.0)],
    ])
    @test MOI.dimension(set) == 4
    @test row_indices(set, 1) == 4:3
    @test isempty(row_indices(set, 1))
    @test row_indices(set, 2) == 4:4
end

function test_set_hash_and_equality()
    set = DisjunctionSet([[MOI.LessThan(1.0)], [MOI.EqualTo(2.0)]])
    other = DisjunctionSet([[MOI.LessThan(1.0)], [MOI.EqualTo(3.0)]])
    @test hash(set) == hash(copy(set))
    @test set != other
    @test length(Set([set, copy(set), other])) == 2
end

function test_set_validation()
    @test_throws ArgumentError DisjunctionSet(
        Vector{MOI.AbstractScalarSet}[])
    @test_throws ArgumentError DisjunctionSet([[MOI.ZeroOne()]])
    @test_throws ArgumentError DisjunctionSet([
        [MOI.LessThan(0.0)],
        [MOI.Nonnegatives(2)],
    ])
end

# The lowering emits one vector constraint per disjunction with the
# activation first, then the indicators, then the rows grouped by
# disjunct.
function test_disjunction_set_lowering()
    model = GDPModel()
    @variable(model, 0 <= x <= 10)
    @variable(model, Y[1:2], Logical)
    @constraint(model, x <= 3, Disjunct(Y[1]))
    @constraint(model, x^2 == 64, Disjunct(Y[2]))
    @disjunction(model, Y)
    reformulate_model(model, Direct())
    crefs = DP._reformulation_constraints(model)
    vector_crefs = filter(crefs) do cref
        constraint_object(cref).set isa DisjunctionSet
    end
    @test length(vector_crefs) == 1
    constraint = constraint_object(only(vector_crefs))
    set = constraint.set
    @test set.inner_sets ==
        [[MOI.LessThan(3.0)], [MOI.EqualTo(64.0)]]
    @test length(constraint.func) == MOI.dimension(set) == 5
    @test isequal_canonical(constraint.func[1],
        one(constraint.func[1])) # top-level activation is the constant 1
    @test coefficient(constraint.func[2], binary_variable(Y[1])) == 1.0
end

# A nested disjunction lowers to its own flat constraint whose
# activation is the parent indicator; the parent carries no rows for it.
function test_lowering_nested()
    model = GDPModel()
    @variable(model, 0 <= x <= 10)
    @variable(model, Y[1:2], Logical)
    @variable(model, W[1:2], Logical)
    @constraint(model, x <= 3, Disjunct(Y[1]))
    @constraint(model, x <= 5, Disjunct(W[1]))
    @constraint(model, x <= 6, Disjunct(W[2]))
    @disjunction(model, W, Disjunct(Y[2]))
    @disjunction(model, Y)
    reformulate_model(model, Direct())
    objs = [constraint_object(cref)
            for cref in DP._reformulation_constraints(model)
            if constraint_object(cref).set isa DisjunctionSet]
    @test length(objs) == 2
    inner = only(filter(c -> c.set.inner_sets ==
        [[MOI.LessThan(5.0)], [MOI.LessThan(6.0)]], objs))
    outer = only(filter(c -> c.set.inner_sets ==
        [[MOI.LessThan(3.0)], MOI.AbstractScalarSet[]], objs))
    @test isequal_canonical(outer.func[1], one(outer.func[1]))
    @test coefficient(inner.func[1], binary_variable(Y[2])) == 1.0
    @test length(outer.func) == MOI.dimension(outer.set) == 4
end

# The transcription entry point: build_constraint promotes mixed
# number/expression vectors (a collapsed constant activation) back to
# a uniform expression vector.
function test_build_constraint_promotion()
    model = GDPModel()
    @variable(model, x)
    @variable(model, z, Bin)
    set = DisjunctionSet([[MOI.LessThan(3.0)]])
    scalars = [1.0 * z, 1.0 * z, 1.0 * x]
    con = JuMP.build_constraint(error, scalars, set)
    @test con isa JuMP.VectorConstraint
    @test con.func === scalars
    @test con.set == set
    mixed = Union{Float64, JuMP.VariableRef}[1.0, z, x]
    con = JuMP.build_constraint(error, mixed, set)
    @test con.func isa Vector{JuMP.AffExpr}
    @test isequal_canonical(con.func[1], one(JuMP.AffExpr))
    @test isequal_canonical(con.func[3], 1.0 * x)
    untyped = Any[1, z, 2.0 * x]
    con = JuMP.build_constraint(error, untyped, set)
    @test con.func isa Vector{JuMP.AffExpr}
    @test isequal_canonical(con.func[3], 2.0 * x)
    @test con.set == set
end

function test_direct_requires_exactly1()
    @test DP.requires_exactly1(Direct())
end

function test_lowering_nested_requires_exactly1()
    model = GDPModel()
    @variable(model, 0 <= x <= 10)
    @variable(model, Y[1:2], Logical)
    @variable(model, W[1:2], Logical)
    @constraint(model, x <= 3, Disjunct(Y[1]))
    @constraint(model, x <= 5, Disjunct(W[1]))
    @constraint(model, x <= 6, Disjunct(W[2]))
    @disjunction(model, W, Disjunct(Y[2]), exactly1 = false)
    @disjunction(model, Y)
    @test_throws ErrorException reformulate_model(model,
        Direct())
end

@testset "DisjunctionSet" begin
    test_set_construction()
    test_set_interval_inner()
    test_set_empty_disjunct()
    test_set_hash_and_equality()
    test_set_validation()
end

@testset "Direct lowering" begin
    test_disjunction_set_lowering()
    test_lowering_nested()
    test_lowering_nested_requires_exactly1()
    test_build_constraint_promotion()
    test_direct_requires_exactly1()
end
