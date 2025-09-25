import DisjunctiveProgramming as DP
using DisjunctiveProgramming
using Test

include("utilities.jl")

# RUN ALL THE TESTS
# include("aqua.jl") # temporary ignore until compat is finalized
include("model.jl")
include("jump.jl")
include("variables/query.jl")
include("variables/logical.jl")
include("variables/creation.jl")
include("constraints/selector.jl")
include("constraints/proposition.jl")
include("constraints/disjunct.jl")
include("constraints/indicator.jl")
include("constraints/bigm.jl")
include("constraints/hull.jl")
include("constraints/fallback.jl")
include("constraints/disjunction.jl")
include("print.jl")
include("solve.jl")

if Base.VERSION >= v"1.9" # extensions require Julia v1.9+
    import Pkg
    Pkg.add(url = "https://github.com/infiniteopt/InfiniteOpt.jl", rev = "master")
    include("extensions/InfiniteDisjunctiveProgramming.jl")
end
