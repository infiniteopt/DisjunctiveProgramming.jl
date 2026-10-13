# [Solution Methods](@id methods_manual)
A technical manual for the reformulation methods. See the respective
[guide](@ref methods_guide) for more information.

## Methods
```@docs
AbstractSolutionMethod
AbstractReformulationMethod
BigM
MBM
Hull
PSplit
CuttingPlanes
Indicator
Direct
```

## Direct Lowering
```@docs
DisjunctionSet
SupportedInnerSet
num_disjuncts
activation_index
indicator_indices
row_indices
```

## Reformulation
```@docs
reformulate_model
reformulate_disjunction
reformulate_disjunct_constraint
reformulate_and_relax
requires_exactly1
requires_variable_bound_info
```

## Extension API
```@docs
GDPSubmodel
copy_and_reformulate
copy_model_with_constraints
prepare_max_M_objective
raw_M
disaggregate_expression
relax_logical_vars
unrelax_logical_vars
collect_all_vars
get_constant
```
