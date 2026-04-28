# API reference

## Cardinalities

```@docs
Cardinality
Finite
CountablyInfinite
Continuum
SymbolicCardinality
isfinite_card
```

## PolySet hierarchy

```@docs
PolySet
FinPolySet
NatSet
IntSet
RealSet
IntervalSet
ProductSet
SumSet
ExpSet
SymbolicSet
cardinality
```

## PolyFunction and DependentFunction

```@docs
PolyFunction
tabulate
untabulate
TABULATE_SIZE_CAP
identity_polyfunction
DependentFunction
indexed_family
```

## Polynomial functors

```@docs
Polynomial
y
zero_poly
one_poly
constant
linear
monomial
representable
positions
direction_at
apply
cardinality_of_apply
is_constant
is_linear
is_monomial
is_representable
is_iso
is_iso_strict
corolla_forest
```

## Lenses

```@docs
Lens
identity_lens
compose
lens_count
polybox
```

## Monoidal products

```@docs
parallel
subst
subst_n
```

## Closure, sections, derivative

```@docs
internal_hom
sections
section_lens
do_nothing_section
eval_lens
derivative
```

## Dynamical systems

```@docs
state_system
is_state_system
moore_machine
dynamical_system
initial_state
trajectory
output_trajectory
state_output_trajectory
juxtapose
wrap
```

## Comonoids = categories

```@docs
Comonoid
SmallCategory
to_category
from_category
validate_category_laws
validate_comonoid
state_system_comonoid
discrete_comonoid
monoid_comonoid
Retrofunctor
identity_retrofunctor
validate_retrofunctor
```

## Cofree comonoid and comodules

```@docs
BehaviorTree
behavior_trees
tree_paths
tree_walk
cofree_comonoid
cofree_unit
cofree_universal
RightComodule
regular_right_comodule
validate_right_comodule
LeftComodule
regular_left_comodule
validate_left_comodule
Bicomodule
regular_bicomodule
validate_bicomodule
```

## Symbolic layer

```@docs
SymbolicPolynomial
SymbolicLens
sympoly
symlens
sym_y
sym_zero
sym_one
sym_id
lift
evaluate
simplify
sym_equal
Rule
rules
to_latex
latex_display
```
