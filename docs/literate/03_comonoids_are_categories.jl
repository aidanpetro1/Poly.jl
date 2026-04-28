# # Comonoids = small categories
#
# Niu/Spivak Chapter 7 (following Ahman–Uustalu) shows that giving a comonoid
# in the monoidal category `(Poly, y, ◁)` is the same data as giving a small
# category. `Poly.jl` makes this concrete with two interconverting types:
#
# * `Comonoid(carrier, eraser, duplicator)` — the polynomial-level data.
# * `SmallCategory(objects, morphisms, dom, cod, identity, composition)` —
#   explicit object/morphism tables.
#
# `to_category` and `from_category` round-trip; `validate_comonoid` checks
# the comonoid laws by translation.

using Poly

# ## The state-system comonoid
#
# Carrier `Sy^S`. Categorically: the *contractible groupoid* on `S` — every
# pair of objects has a unique iso between them.

S = FinPolySet([:a, :b, :c])
cs = state_system_comonoid(S)

# Translate to a `SmallCategory` and inspect the tables.

C = to_category(cs)
cardinality(C.objects), cardinality(C.morphisms)

# Morphisms are encoded as `(domain, direction)` pairs. The direction here is
# the codomain-state, so morphism `(:a, :b)` is "from `:a` to `:b`":

C.dom[(:a, :b)], C.cod[(:a, :b)]

# Identity at `:a` is the "stay-put" arrow:

C.identity[:a]

# Composition follows transitivity: `(a→b) ; (b→c) = (a→c)`.

C.composition[((:a, :b), (:b, :c))]

# `validate_comonoid` confirms the comonoid laws via the category-laws
# translation.

validate_comonoid(cs)

# `validate_comonoid_lens_form` is the same check stated directly on the
# lens data — useful when you want to see the four book laws spelled out
# (δ first-component, two counits, coassoc).

validate_comonoid(cs; mode=:lens)

# ## The discrete category
#
# Carrier `Sy`. One identity morphism per object, no others.

cd = discrete_comonoid(S)
Cd = to_category(cd)
cardinality(Cd.morphisms)         # |S| identities

# Every morphism has matching domain and codomain:

all(Cd.dom[m] == Cd.cod[m] for m in Cd.morphisms.elements)

# ## A monoid as a one-object category
#
# `monoid_comonoid(M, e, op)` produces `BM`: one object whose endomorphisms
# form the monoid `M`.

M = FinPolySet(0:3)
add4 = (a, b) -> mod(a + b, 4)
cm = monoid_comonoid(M, 0, add4)

Cm = to_category(cm)
cardinality(Cm.objects), cardinality(Cm.morphisms)

# The composition table reproduces addition mod 4:

Cm.composition[((:pt, 1), (:pt, 2))]
#-
Cm.composition[((:pt, 3), (:pt, 3))]    # 3 + 3 = 6 ≡ 2 (mod 4)

# Validation catches a deliberately-broken example. Left projection
# (`a * b = a`) has 0 as a left identity but not as a right identity for
# `|M| ≥ 2`, so the right-identity law fails:

bad = monoid_comonoid(M, 0, (a, _b) -> a)
validate_comonoid(bad)

# ## Round-trip
#
# `from_category ∘ to_category` reconstructs the original carrier on the
# nose, and the eraser / duplicator agree extensionally.

cs_round = from_category(to_category(cs))
cs_round.carrier == cs.carrier

# ## Retrofunctors = functors
#
# A morphism of comonoids is a `Retrofunctor`: a `Lens` between the carriers
# satisfying counit-preservation and comultiplication-preservation.
# Per Ahman–Uustalu, these are precisely the *functors* between the
# corresponding categories.

T = FinPolySet([:x, :y_])
cdS = discrete_comonoid(FinPolySet([:a, :b]))
cdT = discrete_comonoid(T)
F = Retrofunctor(cdS, cdT,
                 Lens(cdS.carrier, cdT.carrier,
                      i -> i == :a ? :x : :y_,
                      (_, _b) -> :pt))
validate_retrofunctor(F)

