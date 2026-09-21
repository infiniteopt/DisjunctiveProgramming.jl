"""
    InfiniteGDPModel(args...; kwargs...)

Creates an `InfiniteOpt.InfiniteModel` that is compatible with the 
capabiltiies provided by DisjunctiveProgramming.jl. This requires 
that InfiniteOpt be imported first.

**Example**
```julia
julia> using DisjunctiveProgramming, InfiniteOpt

julia> InfiniteGDPModel()

```
"""
function InfiniteGDPModel end

"""
    InfiniteLogical(prefs...)

Allows users to create infinite logical variables. This is a tag 
for the `@variable` macro that is a combination of `InfiniteOpt.Infinite` 
and `DisjunctiveProgramming.Logical`. This requires that InfiniteOpt be 
first imported.

**Example**
```julia
julia> using DisjunctiveProgramming, InfiniteOpt

julia> model = InfiniteGDPModel();

julia> @infinite_parameter(model, t in [0, 1]);

julia> @infinite_parameter(model, x[1:2] in [-1, 1]);

julia> @variable(model, Y, InfiniteLogical(t, x)) # creates Y(t, x) in {True, False}
Y(t, x)
```
"""
function InfiniteLogical end

"""
    GPSampler(
        [f::AbstractGPs.AbstractGP];
        std_dev_margin::Real = 2.5,
        frac_supports::Real = 0.25,
        detect_uniform_M::Bool = true,
        initial_supports = 4
        )

A Gaussian-process M sampler for the `sampler` field of [`MBM`](@ref)
on infinite models. Instead of solving an M subproblem at every
support, it solves the initial supports, then the supports selected
by an upper-confidence-bound acquisition until `frac_supports` of
them are solved, and fills the remaining supports with the posterior
upper confidence bound `mean + std_dev_margin * sd`. The filled
values are heuristic upper estimates of the exact M values, not
certificates. This requires that AbstractGPs be imported first.

**Arguments**
- `f`: An `AbstractGPs.AbstractGP` prior, used as given, e.g.
  `GP(Matern52Kernel())`; omitting it uses a squared exponential
  kernel with its lengthscale selected by marginal likelihood. The
  prior is fit to support coordinates normalized to `[0, 1]` per
  dimension and to M values standardized to zero mean and unit
  scale, so any lengthscale baked into `f` is relative to the unit
  box.
- `std_dev_margin::Real`: Standard deviations added above the
  posterior mean, both to select the next support to solve and to
  fill the unsolved supports (2.5).
- `frac_supports::Real`: Fraction of the supports to solve exactly,
  in `(0, 1]` (0.25). The initial supports are always solved;
  `frac_supports = 1.0` solves every support.
- `detect_uniform_M::Bool`: If `true` (the default), M values that
  agree at the initial supports are taken to be uniform and used for
  every support. Set it to `false` to always fit the GP, which
  leaves the usual `std_dev_margin * sd` cushion on the unsolved
  supports at the cost of the extra solves.
- `initial_supports`: Number of evenly spaced supports solved before
  the first GP fit (4), or a vector of fractions in `[0, 1]` giving
  their positions along the supports. With `detect_uniform_M`,
  evenly spaced initial supports can read a periodic M as uniform;
  pass unevenly spaced fractions to guard against that.

**Example**
```julia
julia> using DisjunctiveProgramming, InfiniteOpt, AbstractGPs, HiGHS

julia> method = MBM(HiGHS.Optimizer,
           sampler = GPSampler(GP(Matern52Kernel()), std_dev_margin = 4.0))
```
"""
function GPSampler end

"""
    sample_M_values(sampler, objectives, sub, method, support_grids)

Compute the MBM M values at the transcription supports of an infinite
model. `sampler` is the `sampler` field of [`MBM`](@ref),
`objectives` is the array of per-support objective expressions, `sub`
is the transcribed submodel wrapped as a `GDPSubmodel`, `method` is
the `_MBM` data, and `support_grids` is a tuple of the supports of
the infinite parameters (a sorted vector per independent parameter,
a matrix of joint supports per dependent group).
Returns an array of M values shaped like `objectives`, a
scalar when M is uniform across the supports, or `nothing` if an M
subproblem is infeasible. Extensions implement methods that dispatch
on `sampler`: an [`ExhaustiveSampler`](@ref) solves an M subproblem
at every support, while a [`GPSampler`](@ref) solves a subset of the
supports and
fills the rest with a Gaussian-process upper confidence bound.
"""
function sample_M_values(sampler, objectives, sub, method, support_grids)
    error("Unrecognized `sampler` value `$(repr(sampler))` for MBM " *
          "on an infinite model. Use `ExhaustiveSampler()` to solve " *
          "an M subproblem at every support, or a `GPSampler` (with " *
          "AbstractGPs loaded) to estimate M values with a " *
          "Gaussian process.")
end
