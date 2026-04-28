# # Monoidal products
#
# `Poly.jl` exposes four monoidal structures on the category of polynomial
# functors. Each one acts on both polynomials and lenses, and each one has a
# distinct categorical meaning. This tour walks through them with worked
# examples and the main book identities.

using Poly

# ## Coproduct `+`
#
# Niu/Spivak Definition 3.51. Positions are the disjoint union of `p`'s and
# `q`'s positions; direction-sets are inherited from each side.

p = @poly y^2 + y       # 2 positions: one with 2 directions, one with 1
q = @poly y^3 + 1       # 2 positions: one with 3 directions, one constant
p_plus_q = p + q

# Note that `+` is *strictly* non-commutative — positions get tagged `(1, i)`
# from the left summand and `(2, j)` from the right — so `p + q != q + p`
# under `==`. They are isomorphic via `≈` (cardinality-iso).

p + q == q + p
#-
(p + q) ≈ (q + p)

# ## Cartesian product `×` (also `*`)
#
# Niu/Spivak Definition 3.58. Positions are the cartesian product of position
# sets; direction-set at `(i, j)` is the *sum* `p[i] + q[j]`.

p_times_q = p * q       # equivalently `var"×"(p, q)`

# Worked example from the book (Example 3.62):
# `(y^3 + y) × (y^4 + y^2 + 1) ≈ y^7 + 2y^5 + 2y^3 + y`. Each position-pair
# `(i, j)` contributes a position whose direction-cardinality is
# `|p[i]| + |q[j]|`.

a = @poly y^3 + y
b = @poly y^4 + y^2 + 1
(a * b) ≈ (@poly y^7 + 2y^5 + 2y^3 + y)

# ## Parallel product `⊗` (Dirichlet)
#
# Niu/Spivak Definition 3.69. Positions are still cartesian, but
# direction-set at `(i, j)` is the *product* `p[i] × q[j]`. The unit is `y`.

p_par_q = parallel(p, q)        # equivalently `p ⊗ q`

# Example 3.70: `(y^3 + y) ⊗ (y^4 + y^2 + 1)` gets direction-cardinalities
# `{12, 6, 0, 4, 2, 0}` from products `(3,4), (3,2), (3,0), (1,4), (1,2), (1,0)`,
# i.e. `≈ y^12 + y^6 + y^4 + y^2 + 2`.

(@poly y^3 + y) ⊗ (@poly y^4 + y^2 + 1)

# `⊗` distributes over `+`. Niu/Spivak Exercise 3.77:

p1 = @poly y^2
p2 = @poly y
r  = @poly y^3
((p1 + p2) ⊗ r) ≈ ((p1 ⊗ r) + (p2 ⊗ r))

# ## Substitution / composition product `▷` (book `◁`)
#
# Niu/Spivak Definition 6.1. Asymmetric. Positions of `p ▷ q` are pairs
# `(i, j̄)` where `i ∈ p(1)` and `j̄ : p[i] → q(1)` is a function. The
# direction-set at `(i, j̄)` is `Σ_{a ∈ p[i]} q[j̄(a)]`.
#
# The book uses `◁` (U+25C1) which Julia's parser doesn't accept; we use `▷`
# (U+25B7) at multiplication precedence. The named form is `subst`.

(@poly y^2 + y) ▷ (@poly y^3 + 1)
#-
subst((@poly y^2 + y), (@poly y^3 + 1))         # same thing

# Worked example from the book §6.1.3:
# `(y^2 + y) ◁ (y^3 + 1) ≈ y^6 + 3y^3 + 2`. Six positions with
# direction-cardinalities `{6, 3, 3, 3, 0, 0}`.

# `▷` has unit laws on both sides: `p ▷ y ≈ p` and `y ▷ p ≈ p`.

(p ▷ y) ≈ p, (y ▷ p) ≈ p

# **Asymmetry:** `▷` is left-distributive over `+`, but **not** right-distributive.

a = @poly y^2
bb = @poly y
c  = @poly y + 1
((a + bb) ▷ c) ≈ ((a ▷ c) + (bb ▷ c))           # left-distributive
#-
r2 = @poly y^2
lhs = r2 ▷ (bb + bb)                            # r ◁ (y + y)
rhs = (r2 ▷ bb) + (r2 ▷ bb)                     # (r ◁ y) + (r ◁ y) = 2y^2
lhs ≈ rhs                                       # false

# ## Iterated substitution `subst_n`
#
# `subst_n(p, n)` builds `p ▷ p ▷ ... ▷ p` (n copies). By convention `subst_n(p, 0) = y`
# and `subst_n(p, 1) = p`. Used in dynamical-systems modeling for n-step
# evolution (see the [Comonoids tour](03_comonoids_are_categories.md)).

subst_n((@poly y^2), 3) ≈ (@poly y^8)           # y^2 ◁ y^2 ◁ y^2 = y^(2·2·2)

# ## All four products act on lenses too
#
# Each operation is a bifunctor: it acts coherently on lenses as well as
# polynomials. Build a small lens, then check that `f + g`, `f × g`, `f ⊗ g`,
# and `f ▷ g` all type-check and produce the expected dom / cod.

P = @poly y^2
Q = @poly y^3
f = identity_lens(P)
g = identity_lens(Q)
(f + g).dom == (P + Q),  (f * g).dom == (P * Q)
#-
(f ⊗ g).dom == (P ⊗ Q),  (f ▷ g).dom == (P ▷ Q)

# ## Constants and units
#
# - `zero_poly` is the empty polynomial (no positions), unit for `+`,
#   absorbing for `×` and `⊗`.
# - `one_poly` is the singleton constant, unit for `×`.
# - `y` is the identity polynomial, unit for `⊗` and `▷`.
#
# These appear all over the book's identities and `simplify` will use them
# to reduce expressions (see the [Symbolic layer tour](07_symbolic_layer.md)).

zero_poly + p ≈ p,  p * one_poly ≈ p
#-
y ⊗ p ≈ p,  y ▷ p ≈ p
