# [Logical Variables](@id variables_manual)
A technical manual for logical variables. See the respective
[guide](@ref variables_guide) for more information.

## Definition
```@docs
Logical
LogicalVariable
build_variable
add_variable
create_variable
```

## Data Types
```@docs
LogicalVariableRef
LogicalVariableData
LogicalVariableIndex
VariableProperties
```

## Queries
```@docs
binary_variable
has_logical_complement
name
start_value
is_fixed
fix_value
value
get_variable_info
variable_bound_info
```

## Modification
```@docs
set_name
set_start_value
fix
unfix
set_variable_bound_info
variable_copy
```

## General
```@docs
index
owner_model
is_valid
isequal_canonical
delete
```

## Internal
```@docs
DisjunctiveProgramming._free_variable_info
DisjunctiveProgramming._make_variable_object
```
