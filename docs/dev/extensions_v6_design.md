# Extensions v6 — v0.7 design doc

> **Status (2026-05-04).** Draft. Authored after reading the FA paper
> (arXiv 2111.10968v7) end-to-end. Awaiting Q-resolution before
> implementation lands.

> **Phasing context.** v0.6 (PolyAggregation v0.3.0 prereqs) and
> v0.6.1 (paper-faithful Lemma 8.7 + coclosure) shipped 2026-05-04 to
> `main`, tests green. v0.7-partial (full Prop 3.20 bridge) shipped
> the same day. v0.7-main is the work designed below.

## 0. At-a-glance

| # | Item | Paper | File(s) | Lines (est.) | Days | Risk | Blocks |
|---|---|---|---|---|---|---|---|
| 1 | Multi-variable Dirichlet ⊗ on d-Set[c] — type system + ops | Lemma 7.13, Cor 7.15 | new `src/MultiVar.jl`, extends `Polynomial.jl` | ~700 | 6-8 | high | 2, 3, 4, 5 |
| 2 | Theorem 7.19 contravariant equivalence Cat#_lin ↔ Cat#_disc,con | Theorem 7.19, Eq. 64 | new `src/Duality.jl` | ~400 | 4-5 | medium | — |
| 3 | Profunctor ↔ conjunctive bicomodule dictionary | Prop 7.25, Prop 7.27 | extends `CatSharp.jl` | ~300 | 3-4 | medium | — |
| 4 | Generalize `kan_along_bicomodule` to general (c, d) | Prop 6.7, Eq. 59 | extends `Cofree.jl` | ~250 | 3-4 | medium | — |
| 5 | Duoidality natural map (◁ ⊗ ◁) → (⊗ ◁ ⊗) | Prop 7.10, Prop 7.17 | extends `Monoidal.jl` | ~200 | 2-3 | low | — |
| 6 | Symbolic coclosure for non-finite carriers | extends v0.6.1 | extends `Closure.jl`, `Polynomial.jl` (lazy `apply`) | ~250 | 3 | medium | — |
| 7 | Categorical structure on `E` in `BridgeDiagram` (general bases) | Prop 3.20 | extends `CatSharp.jl` | ~150 | 2 | low | — |
| — | **Total** | — | — | **~2250** | **~25 (5 weeks)** | — | — |

**Source.** All seven items come from Spivak/Garner/Fairbanks
*Functorial Aggregation* (arXiv 2111.10968v7). The paper is in the
repo at `poly-book.pdf` (no, that's the Niu/Spivak book) — the FA
paper is `2111.10968v7.pdf` in the user's local uploads.

**Phasing.** Item #1 is the foundation; #2-5 build on it; #6 and #7
are independent of #1 and can ship at any time. PR ordering (a tree
rather than linear):

```
        #6 (independent, no #1 dep)
        #7 (independent, no #1 dep)
        #1 (foundation)
       /  |  |  \
      #2 #3 #4  #5
```

**Out of scope for v0.7** (deferred to v0.8 or later):

- The aggregation framework §8 itself — that's PolyAggregation.jl
  v0.3.0+, not core Poly.jl.
- The Cat# 2-cell structure on `BridgeDiagram` (e.g. `BridgeMorphism`).
  Useful only once Cat# 2-cells are in routine use. Defer.
- Continuous / measure-theoretic versions of the multi-var Dirichlet.
  Different category.

---

## 1. Multi-variable Dirichlet ⊗ on `d-Set[c]` (Lemma 7.13, Cor 7.15)

**Paper.** §7.2 introduces `d-Set[c]` as the category of c-variable
d-valued polynomials and Dirichlet maps (Def 7.11). Lemma 7.13 shows
the functor `Q : d-Dir[c] → d-Set` (taking `p ↦ p(1)`) is a cartesian
monoidal fibration; its opposite `P : d-Set[c] → d-Set` carries the
Dirichlet monoidal structure with formula

    (p_c ⊗_d q)(1)            = p(1) × q(1)
    (p_c ⊗_d q)_a [(i, j)]    = p_a[i] × q_a[j]

(paper Eq. 71). Cor 7.15 shows this monoidal product is closed, with
internal hom `[q, r]_b` given by

    [q, r]_b(1) := d-Set[c](Y^b × q, r)
    [q, r]_b[α] := colim ...    (Eq. 74)

where `Y^b ∈ d-Set[c]` is the polynomial constant at the representable
`y^b ∈ d-Set`.

### 1.1 Type design

The current `Polynomial` type (`src/Polynomial.jl`) is
*single-variable Set-valued*: it encodes `Set → Set` via `positions`
(a `PolySet`) and `direction_at` (each direction-set a `PolySet`).
Multi-var `d-Set[c]` polynomials need:

- A **d-Set** for `p(1)` instead of a single `PolySet`. A d-Set is a
  functor `d → Set`, materialized as a `Dict{ObjectOf_d, PolySet}` plus
  morphism actions `Dict{MorphismOf_d, Function}`.
- A **c-Set** for each direction-set `p_a[i]`. Same shape: dict of
  PolySets per object of c, with morphism actions.

**Proposed types (Q1.1 — sign off):**

```julia
"""
    DSet(category::Comonoid, objects::Dict{Any,PolySet}, morphisms::Dict{Any,Function})

A d-Set is a functor `d → Set` materialized by per-object PolySets and
per-morphism action functions. `category` is the source d as a
Comonoid (= category in Cat#).
"""
struct DSet
    category::Comonoid
    objects::Dict{Any,PolySet}            # ObjectOf_d ↦ p_a(1)
    morphisms::Dict{Any,Function}         # f : a → a' ↦ map p_a → p_{a'}
end

"""
    MultiVarPolynomial(c::Comonoid, d::Comonoid, positions_dset::DSet,
                       directions::Dict{Any,DSet})

A c-variable d-valued polynomial p ∈ d-Set[c]. `positions_dset`
encodes p(1) ∈ d-Set; for each (a ∈ d, i ∈ p_a(1)) tuple,
`directions[(a, i)]` is the c-Set p_a[i].
"""
struct MultiVarPolynomial
    c::Comonoid
    d::Comonoid
    positions::DSet
    directions::Dict{Tuple{Any,Any},DSet}     # (a, i) ↦ p_a[i] as c-Set
end
```

**Q1.1.** Top-level type names: `DSet` and `MultiVarPolynomial`, or
`CSet` (matching Catlab.jl) and `MultiVarPoly`? The Catlab.jl
collision concern is real but low-risk (we import nothing from Catlab
in core Poly.jl per the v0.5 scope decision). Recommendation: ship
`DSet` and `MultiVarPolynomial`; rename later if Catlab integration
becomes a thing.

**Q1.2.** Should `MultiVarPolynomial <: AbstractPolynomial`? The
existing single-var `Polynomial` IS the c=1, d=1 instance of
`MultiVarPolynomial`. Two options:

- **(a)** Make `Polynomial` a subtype distinct from
  `MultiVarPolynomial`, with conversion. Pro: existing code unchanged.
  Con: dispatch ambiguity on `subst`, `parallel`, `+` etc.
- **(b)** Make `Polynomial` an alias for the c=1, d=1 instance of
  `MultiVarPolynomial`. Pro: unified algebra. Con: every existing call
  site allocates the trivial `c = 1, d = 1` boilerplate. Big perf
  regression.

**Recommendation:** **(a)** — separate types, `Polynomial`
unchanged, `MultiVarPolynomial` lives next to it. Conversion via
`as_multivar(p::Polynomial; c=trivial, d=trivial)`.

### 1.2 Operations

```julia
# Eq. 71 binary product.
Base.:*(p::MultiVarPolynomial, q::MultiVarPolynomial; ...)::MultiVarPolynomial
parallel(p::MultiVarPolynomial, q::MultiVarPolynomial)::MultiVarPolynomial   # ⊗

# Identity object.
trivial_multivar(c::Comonoid, d::Comonoid)::MultiVarPolynomial               # I_{c,d}

# Internal hom (Cor 7.15).
internal_hom(q::MultiVarPolynomial, r::MultiVarPolynomial)::MultiVarPolynomial

# Convenience: lift Polynomial to MultiVarPolynomial.
as_multivar(p::Polynomial; c=trivial, d=trivial)::MultiVarPolynomial
```

### 1.3 Tests

- **Identity object:** `parallel(p, trivial_multivar(c, d)) ≈ p`.
- **Associativity:** `parallel(p, parallel(q, r)) ≈ parallel(parallel(p, q), r)`.
- **Single-var collapse:** for `c = trivial`, `d = trivial`,
  `parallel(as_multivar(p), as_multivar(q)) ≈ as_multivar(parallel(p, q))`
  (matches the single-var Dirichlet ⊗).
- **Closure adjunction:** `Poly[c]([q, r]_d, p)` ↔ `Poly[c](q ⊗_d p, r)`.

### 1.4 Out of scope for v0.7

- General colimits in `c-Set` for the closure formula (Eq. 74's
  `colim`). v0.7 ships the formula only for *discrete* c (where the
  colim collapses to a coproduct). The general case requires a
  `colim_in_cset` operation that's a v0.8 item.

---

## 2. Theorem 7.19 contravariant equivalence

**Paper.** Theorem 7.19: weak duality `p ↦ p^∨ = [p, ⊥]_{Cy ⊗ Dy}`
restricts to a contravariant equivalence between `Cat#_lin(C, D)` and
`Cat#_disc,con(C, D)` (linear vs. conjunctive bicomodules over
discrete bases). Eq. 64 generalizes the single-var Eq. 67 from
Example 7.2.

### 2.1 Implementation

Once Item #1 is in place:

```julia
weak_dual_multivar(p::MultiVarPolynomial; c=p.c, d=p.d)::MultiVarPolynomial
# = internal_hom(p, ⊥_{c, d}) where ⊥_{c, d} is the C y ⊗ D y unit.

weak_dual_bicomodule(B::Bicomodule)::Bicomodule
# Wraps weak_dual_multivar with the bicomodule shape preserved.

is_conjunctive(B::Bicomodule)::Bool
ConjunctiveBicomodule(B::Bicomodule)::ConjunctiveBicomodule  # validate-and-wrap
```

### 2.2 Tests

- **Single-var case:** `weak_dual_multivar(as_multivar(p)) ≈
  as_multivar(weak_dual(p))` for the single-var p.
- **Linear ↔ Conjunctive:** `weak_dual_bicomodule(L)` is conjunctive
  for any `L::LinearBicomodule`, and vice versa.
- **Idempotence on reflexive:** `weak_dual^2(B) ≈ B` for B in the
  reflexive subcategory (linear or conjunctive).

---

## 3. Profunctor ↔ conjunctive bicomodule dictionary

**Paper.** Prop 7.25 identifies `Cat#` with a full sub-framed-bicategory
of `Comod(Cat#_disc)`. Prop 7.27 phrases this via weak dualization
explicitly. Together: profunctors `c` ↔ `d` are equivalent to certain
conjunctive bicomodules, and the dictionary is computable.

### 3.1 Implementation

Depends on Item #1 (multi-var ⊗) and Item #2 (weak duality).

```julia
"""
    Profunctor(c::Comonoid, d::Comonoid, ...)

A profunctor c ⇸ d, materialized as a c × d^op-Set (or as a
conjunctive bicomodule via the Prop 7.25 dictionary).
"""
struct Profunctor ... end

profunctor_to_conjunctive(P::Profunctor)::ConjunctiveBicomodule
conjunctive_to_profunctor(B::ConjunctiveBicomodule)::Profunctor

# Round-trip: profunctor_to_conjunctive ∘ conjunctive_to_profunctor ≈ id.
```

### 3.2 Tests

- Round-trip on a small concrete profunctor (e.g. the hom-functor of c).
- Whisker / horizontal-compose interaction: composition of
  conjunctive bicomodules matches profunctor composition.

---

## 4. Generalize `kan_along_bicomodule` to general (c, d)

**Paper.** Prop 6.7 / Eq. 59:

    [q/p]_{d, e} := Σ_{i ∈ p(1)} y^{q ⊳_c p[i]}

generalizing v0.6.1's `coclosure(q, p)` (which is the c = trivial case).

### 4.1 Implementation

Depends on Item #1 (need `q ⊳_c p[i]` for general c).

```julia
kan_along_bicomodule(q::Bicomodule, p::Bicomodule)::Bicomodule
# = the bicomodule [q/p]_{d, e} of Eq. 59.
```

### 4.2 Tests

- **c = trivial case:** `kan_along_bicomodule` matches v0.6.1's
  `coclosure` element-wise.
- **Functoriality:** the universal property of left Kan extension
  (Eq. 58 adjunction) holds for a few sample bicomodules.

---

## 5. Duoidality

**Paper.** Prop 7.10:

    Dirichlet product is **colax monoidal** with respect to ⊳:
    (p ⊳ q) ⊗ (p' ⊳ q') → (p ⊗ p') ⊳ (q ⊗ q')

Prop 7.17 generalizes this to multi-variable.

### 5.1 Implementation

```julia
duoidality(p, q, p_prime, q_prime)::Lens
# = the natural map (p ⊳ q) ⊗ (p' ⊳ q') → (p ⊗ p') ⊳ (q ⊗ q').
```

### 5.2 Tests

- **Naturality:** for a few lens 2-cells, the duoidality map's
  naturality square commutes.
- **Single-var instance:** for c, d trivial, recovers Prop 7.10 exactly.

---

## 6. Symbolic coclosure for non-finite carriers (independent of #1)

**Paper.** v0.6.1's `coclosure(q, p)` requires `q` and `p` to have
FinPolySet positions and direction-sets. The Lemma 8.7 picture for
the *unbounded* list polynomial `u = list_polynomial()` (with
`NatSet()` positions) needs `coclosure(u, u)` to work without
truncation.

### 6.1 Implementation

The blocker is `apply(p, X)` for `p` with non-finite positions. v0.6.1
returns a `SymbolicSet` for that case. v0.7 implements a real lazy
path:

```julia
struct LazyApply <: PolySet
    p::AbstractPolynomial
    X::PolySet
end

cardinality(la::LazyApply) = ...     # symbolic cardinality
in(elt, la::LazyApply) = ...         # membership without enumeration
length(la::LazyApply) = ...          # only well-defined if finite

# coclosure(q, p) with p::Polynomial (FinPolySet positions) and q
# allowed to have non-finite positions: returns Polynomial whose
# direction-set at i is `LazyApply(q, p[i])`.

# coclosure(q, p) with both non-finite: returns a LazyPolynomial
# with NatSet positions and direction-set evaluated lazily per N.
```

### 6.2 Tests

- `coclosure(list_polynomial(), list_polynomial())` constructs without
  error; its positions are NatSet; its direction at N=3 enumerates to
  the same set as `coclosure(u_3, u_3)[3]` from v0.6.1.
- `comonoid_from_list_polynomial(list_polynomial())` builds the full
  Fin^op skeleton (all positions, all morphisms), validates as a
  comonoid via element-wise spot-checks.

---

## 7. Categorical structure on `E` in `BridgeDiagram` (general bases)

**Paper.** Prop 3.20: in the full version, `E` is a *category*, not
just a set. Morphisms in `E` are induced by the bicomodule's
right-coaction action on directions. v0.7-partial materializes `E` as
a set; v0.7-main upgrades to a category.

### 7.1 Implementation

Replace `BridgeDiagram.E::FinPolySet` with `BridgeDiagram.E::Comonoid`
(viewing categories as comonoids in (Poly, y, ◁)). The set-level form
(v0.7-partial) is recovered via `positions(E.carrier)`.

```julia
struct BridgeDiagram
    bicomodule::Bicomodule
    B::Comonoid                        # was: PolySet  (positions as a set)
    E::Comonoid                        # was: FinPolySet
    # π, S, T become retrofunctors instead of plain functions.
    π::Retrofunctor                    # E → B, étale
    S::Retrofunctor                    # B → c
    T::Retrofunctor                    # E → d
    left_lens::Lens                    # backward-compat
    right_lens::Lens                   # backward-compat
end
```

### 7.2 Tests

- For discrete bases, `E.carrier` is `linear(elements_set)` and the
  retrofunctors degenerate to plain set-functions — the v0.7-partial
  form is recovered exactly.
- For general bases (`state_system_comonoid`, `monoid_comonoid`),
  `E.carrier` has non-trivial morphisms, and `bridge_diagram(B)`
  returns a structurally richer object. Pick a small example and
  verify `validate_retrofunctor(bd.π)`.

### 7.3 Out of scope

- 2-cells (morphisms of bridges) — only useful once Cat# 2-cells are
  in routine use. Defer.

---

## 8. Open Qs to resolve before implementation

**Q8.1 (#1).** Top-level type names — `DSet` / `MultiVarPolynomial`
vs. `CSet` / `MultiVarPoly`? See §1.1.

**Q8.2 (#1).** `MultiVarPolynomial <: AbstractPolynomial` or separate
type with conversion? See §1.1.

**Q8.3 (#1).** Where do `DSet` and `MultiVarPolynomial` live —
`src/MultiVar.jl` (new file, lots of types) or extend `Polynomial.jl`
(grows the file)? Recommendation: new file `src/MultiVar.jl`.

**Q8.4 (#2).** Conjunctive analog `c_one_y_con(c)`: ship as part of
#2 or defer? Recommendation: ship as part of #2 — symmetry with
`c_one_y` is valuable.

**Q8.5 (#3).** `Profunctor` as a top-level type, or as a wrapper
around `MultiVarPolynomial`? Recommendation: top-level type with
conversion functions (cleanest API for users).

**Q8.6 (#6).** `LazyApply` as a `PolySet` subtype, or a separate
"lazy enumeration" framework? Recommendation: `PolySet` subtype, fits
the existing lazy-everywhere policy from v0.4.

**Q8.7 (#7).** Backward compat: keep `BridgeDiagram.B::PolySet`
(v0.7-partial) or break to `B::Comonoid` (v0.7-main)? Recommendation:
add `B_comonoid::Union{Nothing,Comonoid}` field, compute on-demand;
keep `B::PolySet` as the primary field. Avoids breaking the
v0.7-partial test surface.

**Q8.8 (phasing).** Ship #1-#5 cumulatively as v0.7.0, or split into
v0.7.0 (just #1-#2) and v0.7.1 (#3-#5)? Recommendation: cumulative.
The overhead of intermediate releases isn't worth the splitting at
this stage.

**Q8.9 (phasing).** Ship #6 and #7 as a separate v0.6.2 patch
(independent of #1) or roll into v0.7.0? Recommendation: roll into
v0.7.0.

**Q8.10 (out of scope).** Cat# 2-cell structure on `BridgeDiagram` —
ever? Recommendation: only once a downstream consumer needs it.

---

## 9. Implementation phasing across PRs

Suggested PR order (1 PR per item, except #6+#7 can land together):

1. **PR #1** — `MultiVarPolynomial` + `DSet` + multi-var ⊗
   (Lemma 7.13, Cor 7.15). Foundation. Extensive type tests.
2. **PR #2** — Theorem 7.19 weak duality + `is_conjunctive` +
   `ConjunctiveBicomodule`.
3. **PR #3** — Profunctor ↔ conjunctive bicomodule dictionary.
4. **PR #4** — Generalized `kan_along_bicomodule` (Prop 6.7).
5. **PR #5** — Duoidality (Prop 7.10, 7.17).
6. **PR #6+#7** (combined) — Symbolic coclosure (Prop 2.16 lazy
   variant) + `BridgeDiagram` E categorical structure (Prop 3.20
   completion).

PRs #6 and #7 are independent of #1 and can ship alongside any of the
others.

## 10. References

- arXiv 2111.10968v7 (FA paper), §6-7 for the bulk of v0.7.
- v0.6 design doc `extensions_v4_design.md` — superseded by this doc
  for the Cat# inspection bundle.
- v0.6 + v0.6.1 handoff `handoff_2026-05-04_v06_v061.md` — what
  shipped before this design doc.
- Memory: `project_poly_v06_v061_shipped.md`,
  `project_poly_outstanding_work.md`,
  `reference_functorial_aggregation_paper.md`.
