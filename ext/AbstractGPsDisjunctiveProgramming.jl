module AbstractGPsDisjunctiveProgramming

import AbstractGPs
import AbstractGPs.KernelFunctions
import DisjunctiveProgramming as DP

################################################################################
#                               SAMPLER CONFIG
################################################################################
# The concrete sampler behind DP.GPSampler; the base package only
# carries the function stub, so constructing one requires AbstractGPs.
struct _GPSampler{F} <: DP.AbstractMBMSampler
    f::F
    std_dev_margin::Float64
    frac_supports::Float64
    detect_uniform_M::Bool
    initial_supports::Union{Int, Vector{Float64}}

    function _GPSampler(
        f::F;
        std_dev_margin::Real = 2.5,
        frac_supports::Real = 0.25,
        detect_uniform_M::Bool = true,
        initial_supports = 4
        ) where {F <: Union{Nothing, AbstractGPs.AbstractGP}}
        std_dev_margin >= 0 || error("`std_dev_margin` must be nonnegative.")
        0 < frac_supports <= 1 || error("`frac_supports` must be in `(0, 1]`.")
        if initial_supports isa Int
            initial_supports >= 2 ||
                error("`initial_supports` must be at least 2.")
        else
            initial_supports = collect(Float64, initial_supports)
            (!isempty(initial_supports) &&
                all(frac -> 0 <= frac <= 1, initial_supports)) ||
                error("`initial_supports` must be fractions in `[0, 1]`.")
        end
        new{F}(f, Float64(std_dev_margin), Float64(frac_supports),
            detect_uniform_M, initial_supports)
    end
end

# Dispatch on the AbstractGPs prior instead of claiming
# `GPSampler(::Any)`; omitting it fits the lengthscale instead.
DP.GPSampler(f::AbstractGPs.AbstractGP; kwargs...) = _GPSampler(f; kwargs...)
DP.GPSampler(; kwargs...) = _GPSampler(nothing; kwargs...)

################################################################################
#                                 GP FITTING
################################################################################
# Normalized to [0, 1]^d so one lengthscale works across dimensions.
# An independent parameter contributes one coordinate; a dependent
# group contributes its joint-support column.
function _support_coords(grids::Tuple)::Vector{Vector{Float64}}
    axis_coords = map(grids) do g
        g isa AbstractMatrix ? [g[:, j] for j in axes(g, 2)] :
            [[v] for v in g]
    end
    coords = [reduce(vcat, getindex.(axis_coords, Tuple(I)))
              for I in vec(CartesianIndices(length.(axis_coords)))]
    dims = eachindex(first(coords))
    mins = [minimum(c[d] for c in coords) for d in dims]
    ranges = [max(maximum(c[d] for c in coords) - mins[d], eps())
              for d in dims]
    return [[(c[d] - mins[d]) / ranges[d] for d in dims]
            for c in coords]
end

# Defaults behind GPSampler(): candidate lengthscales for the
# marginal-likelihood fit (relative to the unit box) and the
# observation-noise nugget.
const _LENGTHSCALES = [0.05, 0.1, 0.2, 0.4, 0.8]
const _JITTER = 1e-8

# A user prior is used as given; the default squared exponential has
# its lengthscale selected by marginal likelihood
function _fit_posterior(
    sampler::_GPSampler,
    X::Vector{Vector{Float64}},
    y::Vector{Float64}
    )
    sampler.f === nothing ||
        return AbstractGPs.posterior(sampler.f(X, _JITTER), y)
    best_posterior, best_log_prob = nothing, -Inf
    for lengthscale in _LENGTHSCALES
        kernel = KernelFunctions.with_lengthscale(
            KernelFunctions.SqExponentialKernel(), lengthscale)
        finite_gp = AbstractGPs.GP(kernel)(X, _JITTER)
        log_prob = AbstractGPs.logpdf(finite_gp, y)
        if log_prob > best_log_prob
            best_posterior = AbstractGPs.posterior(finite_gp, y)
            best_log_prob = log_prob
        end
    end
    return best_posterior
end

function _mean_sd(
    sampler::_GPSampler,
    X::Vector{Vector{Float64}},
    solved::Dict{Int, Float64}
    )
    solved_indices = collect(keys(solved))
    y = [solved[i] for i in solved_indices]
    y_mean = sum(y) / length(y)
    # floored so near-equal solved values still cushion the filled ones
    y_scale = max(sqrt(sum(abs2, y .- y_mean) / max(length(y) - 1, 1)),
        1e-2 * abs(y_mean), 1e-8)
    posterior = _fit_posterior(
        sampler, X[solved_indices], (y .- y_mean) ./ y_scale)
    posterior_mean = AbstractGPs.mean(posterior, X)
    posterior_var = max.(AbstractGPs.var(posterior, X), 0.0)
    return posterior_mean .* y_scale .+ y_mean,
        sqrt.(posterior_var) .* y_scale
end

################################################################################
#                              M VALUE SAMPLING
################################################################################
# Solve M at max-UCB selected supports, fill the rest with the bound
function DP.sample_M_values(
    sampler::_GPSampler,
    objectives::AbstractArray,
    sub::DP.GDPSubmodel,
    method::DP._MBM,
    support_grids::Tuple
    )
    indices = collect(CartesianIndices(objectives))
    n = length(indices)
    solved = Dict{Int, Float64}()
    solve_at(index::Int) = begin
        M_val = DP.raw_M(sub, objectives[indices[index]], method)
        M_val === nothing && return false
        solved[index] = M_val
        return true
    end
    # an evenly spaced initial count, or user-given fractions
    fractions = sampler.initial_supports isa Int ?
        range(0, 1, length = sampler.initial_supports) :
        sampler.initial_supports
    for index in unique(1 .+ round.(Int, fractions .* (n - 1)))
        solve_at(index) || return nothing
    end
    if sampler.detect_uniform_M
        # a uniform M needs no fit
        probes = collect(values(solved))
        all(==(first(probes)), probes) && return first(probes)
    end
    solve_target = min(ceil(Int, sampler.frac_supports * n), n)
    X = _support_coords(support_grids)
    while length(solved) < solve_target
        means, sds = _mean_sd(sampler, X, solved)
        acquisition = means .+ sampler.std_dev_margin .* sds
        for index in keys(solved)
            acquisition[index] = -Inf
        end
        solve_at(argmax(acquisition)) || return nothing
    end
    M_vals = Array{Float64}(undef, size(objectives))
    if length(solved) == n # nothing left to estimate
        for (index, I) in enumerate(indices)
            M_vals[I] = solved[index]
        end
        return M_vals
    end
    means, sds = _mean_sd(sampler, X, solved)
    for (index, I) in enumerate(indices) # exact M values are nonnegative
        M_vals[I] = get(solved, index,
            max(means[index] + sampler.std_dev_margin * sds[index], 0.0))
    end
    return M_vals
end

end
