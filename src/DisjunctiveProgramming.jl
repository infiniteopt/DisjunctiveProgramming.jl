module DisjunctiveProgramming

# Import and export JuMP 
import Reexport 
Reexport.@reexport using JuMP

# Use Meta for metaprogramming
using Base.Meta

# Create aliases
import JuMP.MOI as _MOI
import JuMP.MOIU.CleverDicts as _MOIUC
import JuMP.Containers as _JuMPC

# Load in the source files
include("datatypes.jl")
include("model.jl")
include("logic.jl")
include("variables.jl")
include("constraints.jl")
include("macros.jl")
include("reformulate.jl")
include("bigm.jl")
include("hull.jl")
include("indicator.jl")
include("print.jl")
include("extension_api.jl")

# Define additional stuff that should not be exported
const _EXCLUDE_SYMBOLS = [Symbol(@__MODULE__), :eval, :include]

# Following JuMP, export everything that doesn't start with a _ 
for sym in names(@__MODULE__, all = true)
    sym_string = string(sym)
    if sym in _EXCLUDE_SYMBOLS || startswith(sym_string, "_") || startswith(sym_string, "@_")
        continue
    end
    if !(Base.isidentifier(sym) || (startswith(sym_string, "@") && Base.isidentifier(sym_string[2:end])))
        continue
    end
    @eval export $sym
end

# export the single character operators (excluded above)
export ∨, ∧, ¬, ⇔, ⟹

end # end of the module