---
title: >-
  DisjunctiveProgramming.jl: A DisjunctiveProgramming extension to JuMP.jl
tags:
  - Julia
  - MINLP
  - Disjunctive Programming
  - Logical Constraints
authors:
  - name: Daniel Nguyen
    affiliation: 1
  # - name: Hector David Perez
  #   affiliation: "?"
  - name: Joshua Pulsipher
    corresponding: true
    affiliation: 1
affiliations:
 - name: University of Waterloo
   index: 1
date:  25 November 2026
bibliography: paper.bib
---

# Summary

`DisjunctiveProgramming.jl` is a Julia package that brings Generalized
Disjunctive Programming (GDP) [@raman1994modelling; @grossmann2013systematic] to
`JuMP.jl`. The package lets users declare logical variables (True/False),
disjunctions, and logical propositions using familiar syntax. The workflow from
a GDP to a mixed-integer program (MIP) that solvers readily accept is automated,
and the package offers an array of reformulation techniques for producing the
final MIP.

The current version of the package also extends other Julia packages (e.g.,
`InfiniteOpt.jl` [@pulsipher2022infiniteopt] and `MathOptAI.jl`).

# Problem Class

`DisjunctiveProgramming.jl` targets optimization problems that contain
continuous and discrete decisions. It represents discrete decisions as
disjuncts, which contain constraints that hold when their logical indicators are
True. Such problems are known as Generalized Disjunctive Programs in the process
systems engineering literature [@grossmann2013systematic;
@trespalacios2014review].


GDP is used to model alternative sets of constraints, which can be linked
through logical propositions. The components are as follows:

- **Global constraints** ($g(x) \leq 0$): constraints that must always hold,
  regardless of which disjuncts are selected.
- **Logical variables** ($Y_{ki}$): True/False variables that indicate whether
  disjunct $i$ of disjunction $k$ is selected.
- **Disjuncts** ($i \in D_k$): the alternatives within disjunction $k$. Each
  pairs a logical variable $Y_{ki}$ with constraints $h_{ki}(x) \leq 0$ that
  must hold when $Y_{ki}$ is True.
- **Disjunctions** ($k \in K$): the choices to be made. Each joins its disjuncts
  with the "or" operator ($\bigvee$).
- **Logical constraints** ($\Omega(Y) = \text{True}$): rules that relate the
  logical variables, such as selecting exactly one disjunct per disjunction or
  requiring one choice whenever another is made.

Together, these components form the general GDP [@raman1994modelling]:

$$
\begin{aligned}
\min_{x, Y} \quad & f(x) \\
\text{s.t.} \quad & g(x) \leq 0 \\
& \bigvee_{i \in D_k} \begin{bmatrix} Y_{ki} \\ h_{ki}(x) \leq 0 \end{bmatrix},
  && k \in K \\
& \Omega(Y) = \text{True} \\
& x \in X, \quad Y_{ki} \in \{\text{True}, \text{False}\},
  && k \in K, \; i \in D_k
\end{aligned}
$$

where $X$ is the domain of the decision variables.

To solve a GDP, each logical variable $Y_{ki}$ is replaced by a binary variable
$y_{ki}$, and each disjunction is rewritten with algebraic constraints. The two
classical reformulations are Big-M [@raman1994modelling]:

$$
\begin{aligned}
& h_{ki}(x) \leq M_{ki} (1 - y_{ki}), && k \in K, \; i \in D_k \\
& \textstyle\sum_{i \in D_k} y_{ki} = 1, && k \in K
\end{aligned}
$$

where $M_{ki}$ is large enough that the constraint is inactive when $y_{ki} =
0$, and Hull [@balas1985disjunctive]:

$$
\begin{aligned}
& x = \textstyle\sum_{i \in D_k} v_{ki}, && k \in K \\
& y_{ki} \, h_{ki}(v_{ki} / y_{ki}) \leq 0, && k \in K, \; i \in D_k \\
& y_{ki} \, x^L \leq v_{ki} \leq y_{ki} \, x^U, && k \in K, \; i \in D_k \\
& \textstyle\sum_{i \in D_k} y_{ki} = 1, && k \in K
\end{aligned}
$$

where $v_{ki}$ are copies of $x$ for each disjunct and $[x^L, x^U]$ are the
bounds of $x$. Hull gives a tighter continuous relaxation, but adds variables
and constraints.


# Statement of need

`DisjunctiveProgramming.jl` is intended for researchers and practicitioners that
require logic in their optimization problems. Such problems could arise in areas
of scheduling, plant configuration, energy systems, and the broader process
system engineering field.

Unless a solver explicitly supports discrete logic, it requires problems in MIP
form to model discrete choices. A MIP is solved with algorithms such as branch
and bound, in which relaxed versions of the problem are solved repeatedly. The
search space of the relaxed problem can grow or shrink depending on how the MIP
is posed [@trespalacios2014review; @kronqvist2025fifty], as shown in
\autoref{fig:disks}. The number of constraints and variables introduced must
also be considered.

For optimization models that require discrete logic, it is often more
interpretable to formulate the problem with True/False logic through
disjunctions than as a MIP in the traditional Big-M [@raman1994modelling] or
Hull [@balas1985disjunctive] form. This is especially true when problems have
multiple layers of logic or nested logic. GDP provides an abstraction layer that
enables users without knowledge of reformulation techniques to pose problems and
recover interpretable solutions [@grossmann2013systematic].

In the modern literature, techniques such as Multiple Big-M
[@trespalacios2015mbm] and P-Split [@kronqvist2022psplit], which are variations
of Big-M and Hull, have been shown to reduce solve times. These techniques are
more involved to formulate, and some require solving subproblems.
`DisjunctiveProgramming.jl` enables users to test all of these techniques with
one keyword argument in the `optimize!` call.

# State of the field

The Statement of need describes the typical hurdles modelers face when solving a
problem initially posed as a GDP. A few tools can reformulate a GDP into a MIP,
and they can be compared by their ecosystems and the reformulations they offer.

- **`Pyomo.GDP`** [@chen2022pyomo] (Python)

  `Pyomo.GDP` extends the Pyomo modeling language, similar to how
  `DisjunctiveProgramming.jl` extends JuMP. It offers a comparable set of
  reformulations (Big-M, Multiple Big-M, Hull, and cutting planes
  [@trespalacios2016cutting]) and is widely used in GDP research.

- **GAMS EMP/LogMIP** [@gams2026emp] (GAMS)

  GAMS is a commercial modeling system that supports GDP through LogMIP 2.0,
  which is part of its Extended Mathematical Programming (EMP) framework. Its
  documented reformulations are Big-M, Hull, and indicator constraints.

- **`DisjunctiveProgramming.jl` v0.3.3** [@perez2023disjunctiveprogramming]
  (Julia)

  The current version of `DisjunctiveProgramming.jl` is a complete redesign of
  the original implementation. The previous version supported only two
  reformulation techniques and did not defer reformulation as the current
  package does. Version 0.3.3 reformulated each disjunction as it was declared,
  so the original GDP was not retained.

- **This package: `DisjunctiveProgramming.jl` v0.8.0** (Julia)

  `DisjunctiveProgramming.jl` supports many of the same reformulations as
  `Pyomo.GDP` and also supports vector and conic constraint sets within
  disjuncts [@bernal2024convex]. Recent work also allows disjunct constraints to
  contain decision functions that vary over continuous domains such as space,
  time, or uncertainty [@gondosiswanto2025infiniteopt].

# Software design

`DisjunctiveProgramming.jl` maintains a separation between the GDP information
and the MIP formulation. A `GDPModel` is, in essence, a JuMP model that contains
extra logical information (logical variables, disjunct constraints, logical
constraints, etc.). This logical information is used to reformulate the model
into its MIP form through subtypes of `AbstractReformulationMethod`. Because of
this separation, the same `GDPModel` can be reformulated multiple times.

![Workflow of `DisjunctiveProgramming.jl`. A `GDPModel` stores the GDP and is
reformulated when `optimize!` is called. The stored GDP can be solved again with
another method.\label{fig:workflow}](figures/workflow.png){ width=100% }

Each reformulation method is a subtype of `AbstractReformulationMethod`, and
Julia's multiple dispatch selects its implementation, so new methods can be
added without changing the modeling interface. The same mechanism supports
extensions within the Julia ecosystem, such as `InfiniteOpt.jl`
[@pulsipher2022infiniteopt], which supports `InfiniteModel`s containing new
constraint types such as ODEs and PDEs.

A disadvantage of this design is that the problem cannot be solved directly with
decomposition techniques such as logic-based outer approximation
[@turkay1996logic] and branch and bound. `DisjunctiveProgramming.jl` addresses
this by offering `DisjunctionSet`, a MathOptInterface set that passes each
disjunction directly to solvers that support it. `DisjunctiveAlgorithms.jl`
implements logic-based outer approximation using this set as a proof of concept.

# Research impact statement

`DisjunctiveProgramming.jl` has been used in the literature for production
scheduling [@mazzadi2026scheduling], quantum annealing [@macielxavier2024qubo],
and nested disjunctions [@perez2023extensions]. It has also been used to
generalize Multiple Big-M, P-Split, cutting planes, and logic-based outer
approximation to InfiniteGDP and benchmark them [@nguyen2026infinitegdp].

The package also provides extensions for three other Julia packages:
`InfiniteOpt.jl` for InfiniteGDP [@gondosiswanto2025infiniteopt], `MathOptAI.jl`
for embedding decision trees inside optimization problems as GDPs, and
`AbstractGPs.jl` for approximating Multiple Big-M values over infinite domains
with Gaussian processes [@nguyen2026infinitegdp].

# Example

Consider an optimization problem whose feasible region is described by three
disjoint disks. Each disk is represented by a disjunct that contains its disk
constraint.

$$
\begin{aligned}
\min_{x, y, Y} \quad & (x - 0.2)^2 + (y - 5)^2 \\
\text{s.t.} \quad & \bigvee_{i \in \{1, 2, 3\}}
  \begin{bmatrix} Y_i \\ (x - a_i)^2 + (y - b_i)^2 \leq 1 \end{bmatrix} \\
& \text{Exactly}(1, Y_1, Y_2, Y_3) = \text{True} \\
& 0 \leq x \leq 8, \quad 0 \leq y \leq 5.5 \\
& Y_i \in \{\text{True}, \text{False}\}, \quad i \in \{1, 2, 3\}
\end{aligned}
$$

where $(a_1, b_1) = (1, 1)$, $(a_2, b_2) = (4, 4.5)$, and $(a_3, b_3) = (7, 1)$
are the centers of the three disks.

`DisjunctiveProgramming.jl` implements this GDP as follows:

```julia
using DisjunctiveProgramming, Gurobi

model = GDPModel(Gurobi.Optimizer)
@variable(model, 0 <= x <= 8)
@variable(model, 0 <= y <= 5.5)
@variable(model, Y[1:3], Logical)
centers = [(1, 1), (4, 4.5), (7, 1)]
for (i, (a, b)) in enumerate(centers)
    @constraint(model, (x - a)^2 + (y - b)^2 <= 1, Disjunct(Y[i]))
end
@disjunction(model, Y)
@objective(model, Min, (x - 0.2)^2 + (y - 5)^2)

optimize!(model, gdp_method = Hull())

######################## ALTERNATIVE METHODS #######################
# optimize!(model, gdp_method = BigM(100))
# optimize!(model, gdp_method = MBM(Gurobi.Optimizer))
# optimize!(model, gdp_method = PSplit([[x], [y]]))
# optimize!(model, gdp_method = CuttingPlanes(Gurobi.Optimizer))
```


To illustrate, the corresponding Big-M and Hull formulations are as follows.

Big-M:

$$
\begin{aligned}
\min_{x, y, z} \quad & (x - 0.2)^2 + (y - 5)^2 \\
\text{s.t.} \quad & (x - a_i)^2 + (y - b_i)^2 \leq 1 + M (1 - z_i),
  && i \in \{1, 2, 3\} \\
& z_1 + z_2 + z_3 = 1 \\
& 0 \leq x \leq 8, \quad 0 \leq y \leq 5.5 \\
& z_i \in \{0, 1\}, && i \in \{1, 2, 3\}
\end{aligned}
$$

Hull:

$$
\begin{aligned}
\min_{x, y, x_i, y_i, z} \quad & (x - 0.2)^2 + (y - 5)^2 \\
\text{s.t.} \quad & x = x_1 + x_2 + x_3, \quad y = y_1 + y_2 + y_3 \\
& (x_i - a_i z_i)^2 + (y_i - b_i z_i)^2 \leq z_i^2, && i \in \{1, 2, 3\} \\
& 0 \leq x_i \leq 8 z_i, \quad 0 \leq y_i \leq 5.5 z_i, && i \in \{1, 2, 3\} \\
& z_1 + z_2 + z_3 = 1 \\
& z_i \in \{0, 1\}, && i \in \{1, 2, 3\}
\end{aligned}
$$

The feasible region and the two relaxations are shown in \autoref{fig:disks}.

![The three-disk example. (a) The GDP minimizes the squared distance to the
star; the optimum lies on the second disk. (b) and (c) Continuous relaxations of
the Big-M and Hull reformulations, with each relaxation's minimizer (open
circle) and lower bound.\label{fig:disks}](figures/disks.png){ width=100% }


# AI usage disclosure

Generative AI tools, including Claude Code (Anthropic), were used to assist with
software development (specifically test writing, debugging, and docstrings),
documentation drafting, and drafting and language editing of this paper,
including grammar, mathematical notation, and figures. AI tools were not used to
make autonomous design, implementation, or scientific decisions. All AI-assisted
code was thoroughly verified against independent reference implementations and
covered by the test suite. All AI-assisted text was reviewed and edited by the
authors, and technical claims were checked against the implementation, tests,
documentation, and cited literature. The authors are responsible for the final
content of the manuscript, code, and documentation. All pull requests are public
and available for review at
https://github.com/infiniteopt/DisjunctiveProgramming.jl.

# Acknowledgements

We acknowledge contributions from Hector D. Perez, Shivank Joshi, and Ignacio E.
Grossmann during the genesis of this project, as well as support from the
Natural Sciences and Engineering Research Council of Canada under grant
RGPIN-202403997 and support provided from the Department of Chemical Engineering
at the University of Waterloo.

# References
