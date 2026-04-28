# # Cofree comonoid and comodules
#
# Niu/Spivak Chapter 8 builds the *cofree comonoid* `T_p` on a polynomial
# `p`: a comonoid whose objects are `p`-trees and whose morphisms are paths.
# Together with comodules and bicomodules, this generalizes presheaves and
# discrete opfibrations to a polynomial-functor setting.
#
# This tour walks through the construction at small depth.

using Poly

# ## A small `p` and its trees
#
# Take `p = y + 1`: one looping action and one halt. A `p`-tree is a finite
# sequence of "loop" or "stop" choices.

p = Polynomial(FinPolySet([:run, :halt]),
               i -> i == :run ? FinPolySet([:tick]) :
                                FinPolySet(Symbol[]))

# `behavior_trees(p, d)` enumerates all trees of depth `≤ d`. Trees grow as
# towers of exponentials in `d` — keep `d` small for non-trivial `p`.

trees1 = behavior_trees(p, 1)
length(trees1)

# ### Paths and walks
#
# `tree_paths(t)` is the list of all paths through `t`, including the empty
# path `()`. `tree_walk(t, π)` returns the destination subtree.

t = first(t for t in trees1 if !isempty(t.children))
tree_paths(t)
#-
tree_walk(t, (:tick,)).label

# ## The cofree comonoid `T_p^{(d)}`
#
# `cofree_comonoid(p, depth)` is the depth-bounded truncation of `T_p`. Its
# carrier has all `p`-trees of depth `≤ depth` as positions, and paths
# through each tree as that tree's directions.
#
# - **Eraser** ε: at every tree, the identity direction is the empty path.
# - **Duplicator** δ: at a tree `t`, sends `t ↦ (t, jbar_t)` where
#   `jbar_t(π) = tree_walk(t, π)`. On directions, concatenates paths.

Tp = cofree_comonoid(p, 2)
cardinality(Tp.carrier.positions)

# `Tp` validates as a comonoid in both modes:

validate_comonoid(Tp), validate_comonoid(Tp; mode=:lens)

# As a category, `to_category(Tp)` has trees as objects and paths as
# morphisms — composition is concatenation, identity is the empty path.

C_T = to_category(Tp)
cardinality(C_T.objects), cardinality(C_T.morphisms)

# ## The labeling lens `cofree_unit`
#
# `cofree_unit(p, d) : T_p^{(d)} → p` extracts the root label of each tree
# (on positions) and lifts a `p`-direction to the singleton path `(a,)` (on
# directions). Together with `cofree_universal`, this characterizes `T_p` as
# the cofree comonoid: every comonoid `c` with a labeling `c → p` factors
# uniquely through `T_p`.

ε_p = cofree_unit(p, 2)
ε_p.dom == Tp.carrier,  ε_p.cod == p

# ## The universal property
#
# Build a state-system comonoid on `S = {s1, s2}`, equip it with a
# labeling `cs.carrier → p`, and ask `cofree_universal` for the unique
# retrofunctor factoring the labeling.

S  = FinPolySet([:s1, :s2])
cs = state_system_comonoid(S)
labeling = Lens(cs.carrier, p,
                _ -> :run,
                (_, _) -> S.elements[1])
F = cofree_universal(cs, labeling, 2)

# The substantive property: composing `F.underlying` with `cofree_unit`
# recovers the original labeling exactly.

compose(F.underlying, cofree_unit(p, 2)) == labeling

# (Note: under depth-truncation the strict comonoid-morphism laws don't
# hold for a comonoid with non-trivial walks — see the docstring on
# `cofree_universal`. The element-wise universal property above is the
# substantive content.)

# ## Right comodules
#
# A *right comodule* over a comonoid `c` is a polynomial `X` with a
# coaction `λ : X → X ▷ c.carrier` satisfying counit + coassociativity.
# The *regular* right comodule on `c` is `(c.carrier, c.duplicator)` —
# validates iff `c` itself is a valid comonoid.

cs2 = state_system_comonoid(FinPolySet([:a, :b, :c]))
M_R = regular_right_comodule(cs2)
validate_right_comodule(M_R)

# `RightComodule` constructor type-checks the coaction shape (`dom ==
# carrier`, `cod == carrier ▷ base.carrier`) but does not check the laws —
# you call `validate_right_comodule` for that. Same on the left side
# with `LeftComodule` / `validate_left_comodule`.

M_L = regular_left_comodule(cs2)
validate_left_comodule(M_L)

# ## Bicomodules
#
# A bicomodule `(c, X, d)` has both a left `c`-coaction and a right
# `d`-coaction satisfying compatibility. Niu/Spivak Chapter 8: bicomodules
# correspond to *prafunctors* between the categories `cat(c)` and `cat(d)`.

B = regular_bicomodule(cs2)
validate_bicomodule(B)

# `validate_bicomodule` checks both comodule laws on each side plus the
# compatibility square element-wise. The implementation handles all this
# without needing to construct the associator of `▷` explicitly — see
# `validate_bicomodule`'s docstring for the unfolded form.
