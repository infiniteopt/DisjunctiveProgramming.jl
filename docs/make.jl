using DisjunctiveProgramming
using Documenter
makedocs(
    sitename = "DisjunctiveProgramming.jl",
    modules  = [DisjunctiveProgramming],
    pages=[
        "Home" => "index.md",
        "API" => "api.md"
    ],
    checkdocs = :none
)
deploydocs(;
    repo="github.com/infiniteopt/DisjunctiveProgramming.jl",
)
