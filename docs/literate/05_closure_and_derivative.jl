# # Closure, sections, and the derivative
#
# Niu/Spivak Chapter 4 builds three constructions that come for free once
# `⊗` is in place: the closure `[q, r]`, the section space `Γ(p)`, and the
# derivative `ṗ`. This tour walks through each one.

using Poly

# ## The closure `[q, r]`
#
# `internal_hom(q, r)` builds the polynomial `[q, r]` such that
# `Poly(p ⊗ q, r) ≅ Poly(p, [q, r])` (Proposition 4.85). A position of
# `[q, r]` *is* a lens `q → r`; the direction-set at that position is
# `Σ_{j ∈ q(1)} r[f₁(j)]`.

q = @poly y + 1
r = @poly y^2
qr = internal_hom(q, r)

# Two checks. First, the position-count of `[q, r]` equals `|Poly(q, r)|` by
# construction:

cardinality(qr.positions) == lens_count(q, r)

# Second, the closure adjunction's cardinality version:

p = @poly y^2 + y
lens_count(parallel(p, q), r) == lens_count(p, internal_hom(q, r))

# ### Niu/Spivak Example 4.81 identities
#
# `[y^A, y] ≈ Ay` and `[Ay, y] ≈ y^A`.

A   = FinPolySet([:a, :b, :c])
yA  = representable(A)               # y^A
Ay  = linear(A)                      # Ay
internal_hom(yA, y) ≈ Ay
#-
internal_hom(Ay, y) ≈ yA

# ### The evaluation lens
#
# By the closure adjunction, the identity on `[q, r]` corresponds to a lens
# `[q, r] ⊗ q → r`. That's `eval_lens(q, r)`.

ev = eval_lens(q, r)
ev.dom == parallel(internal_hom(q, r), q),  ev.cod == r

# ## Sections `Γ(p) = Poly(p, y)`
#
# A *section* of `p` picks one direction at every position. By
# Niu/Spivak Eq. (3.35), `Γ(p) ≅ Π_{i ∈ p(1)} p[i]`.

p2 = @poly y^2 + y
secs = sections(p2)
cardinality(secs)

# `section_lens(p, σ)` builds the corresponding lens `p → y` from a chosen
# section dict `σ`.

σ = first(secs.elements)
γ = section_lens(p2, σ)
γ.cod == y

# ### `Γ(p + q) ≈ Γ(p) × Γ(q)` (Niu/Spivak Prop 3.39)
#
# Sections of a sum are pairs of sections. Cardinality-wise:

p3 = @poly y^2
q3 = @poly y^3
cardinality(sections(p3 + q3)).n ==
    cardinality(sections(p3)).n * cardinality(sections(q3)).n

# ## The do-nothing section
#
# On a state system `Sy^S`, the canonical section `ε : Sy^S → y` picks the
# direction-equal-to-the-position at every state. Niu/Spivak Example 4.43.
# This is *exactly* the eraser of [`state_system_comonoid`](@ref) — see the
# [Comonoids tour](03_comonoids_are_categories.md).

S = FinPolySet([:s1, :s2, :s3])
ε = do_nothing_section(S)
ε.on_directions.f(:s2).f(:pt)            # = :s2 — picks the matching direction

# ## Derivative `ṗ`
#
# Niu/Spivak Example 3.22:
#
# ```
# ṗ = Σ_{i ∈ p(1)} Σ_{a ∈ p[i]} y^{p[i] − {a}}
# ```
#
# Each position is a pair `(i, a)` — a "position with a marked direction" —
# and the direction-set at `(i, a)` is `p[i]` minus that marked direction.

ṗ = derivative(p2)

# Cardinality check: `|ṗ(1)|` equals the total number of directions of `p`.

expected = sum(cardinality(direction_at(p2, i)).n for i in p2.positions.elements)
cardinality(ṗ.positions).n == expected

# ## Putting it together: hom-set adjunction
#
# A small worked example showing that `Poly(p ⊗ q, r)` and `Poly(p, [q, r])`
# really are in bijection (cardinality-only check, since enumerating both
# explicitly takes more code).

p4 = @poly y + 1
q4 = @poly y + 1
r4 = @poly y^2
lens_count(parallel(p4, q4), r4) == lens_count(p4, internal_hom(q4, r4))
