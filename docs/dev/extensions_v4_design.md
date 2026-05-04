# Poly.jl — Extensions v4 Design Doc (v0.6 release)

> **Status**: SKETCH, 2026-05-03. Not yet signed off. Open questions in §7 — please resolve in a structured Q&A round before implementation begins, as with v1 / v2 / v3.

---

## 0. Summary

| # | Item | Class | Breaks API? | PR size | Depends on |
|---|---|---|---|---|---|
| 1 | `bridge_diagram(::Bicomodule)` — extract `(s, π, t)` Σ_t∘Π_π∘Δ_s factorization | New introspection | No (additive) | M | — |
| 2 | `is_linear` / `is_conjunctive` predicates + `LinearBicomodule` / `ConjunctiveBicomodule` markers | New classification | No (additive) | S | #1 |
| 3 | `weak_dual(p)` — `[p, y]` in single-variable Dirichlet | New operation | No (additive) | S | — |
| 4 | List polynomial `u = Σ_{N∈ℕ} y^N` and `[u/u] ≅ Fin^op` | New constructor | No (additive) | S | Symbolic positions |
| 5 | `linear_bicomodule_from_span` / `span_from_linear_bicomodule` — Cor 6.17 dictionary | New conversion | No (additive) | M | #2 |

**Source.** All five items come from Spivak / Garner / Fairbanks, *Functorial Aggregation* (arXiv 2111.10968v7, Jan 2025). See `reference_functorial_aggregation_paper.md` in memory and the per-item paper-section pointers below.

**Phasing.** v0.6 = the "Cat♯ inspection + duality bundle" (#1–#5). Multi-variable Dirichlet ⊗ on `d-Set[c]` (paper §7.2-7.3) and the Cat♯ left-Kan extension generalization (paper Prop 6.7) are deferred to **v0.7**. The aggregation framework (paper §8) is moved to a separate library, **PolyAggregation.jl**, mirroring the 2026-05-02 PolyMarkov.jl decision — see §6 for the brief and the handoff plan.

**Where the codebase stands today.** v0.5 shipped `validate_retrofunctor_forward` for partial-image retrofunctors, closing the self-validation gap left by v0.4.x's `base_change_left/right`. All test files green on Julia 1.10.5. We have: `Bicomodule` with `left_base`/`right_base`/`left_coaction`/`right_coaction` (Cofree.jl:1176), `Retrofunctor` (Comonoid.jl:1235), `parallel` for single-var Dirichlet ⊗ (Monoidal.jl:323), `kan_along_bicomodule` and `kan_2cat` (Cofree.jl:3408, 3646), `free_labeled_transition_comonoid` (Comonoid.jl:684). No `bridge_diagram`, no weak dual, no linear/conjunctive predicates.

---

## 1. `bridge_diagram(::Bicomodule)` — extract `(s, π, t)` factorization

**Paper.** Proposition 3.20: every prafunctor `p: c-Set → d-Set` factors as `Σ_t ∘ Π_π ∘ Δ_s` for a span `E ←ˢ B →ᵗ D` with `t` étale (a discrete opfibration of categories). Currently we build `Bicomodule`s by handing in the carrier polynomial and the two coactions; we have no way to ask "what is the canonical span+étale presentation of this bicomodule?"

### 1.1 Proposed design

```julia
# src/CatSharp.jl   (new file)

struct BridgeDiagram
    bicomodule::Bicomodule
    e::Comonoid              # left base (= bicomodule.left_base)
    b::Comonoid              # the carrier viewed as a comonoid via ρ
    d::Comonoid              # right base (= bicomodule.right_base)
    s::Retrofunctor          # E L99 B,  the "Σ" leg
    pi::Retrofunctor         # B → D,    the "Π" leg, étale
    t::Retrofunctor          # B L99 D,  the "Σ_T" leg (étale = bijective on outfacing)
end

bridge_diagram(M::Bicomodule) :: BridgeDiagram
```

Construction:
- The carrier `b` is built from `M.carrier` plus the *right* coaction (which already gives a right-comodule structure → `c`-set per position via Prop 5.10).
- `s` reads off the left coaction's effect on positions/directions (Σ leg).
- `pi` is the position map → `D`'s objects, étale because each position lands on exactly one object with bijective outfacing (this is what makes the comodule structure consistent).
- `t` is the étale completion that matches `pi`'s position map.

**Round-trip.** `Bicomodule(::BridgeDiagram)` reconstructs the original (up to iso). Round-trip law tested on every Bicomodule in the test suite.

### 1.2 Tests

- Identity bicomodule on `c`: bridge diagram is `(id, id, id)`.
- Bicomodule built by `whisker_left(retro, M)`: `s` matches `retro`, `pi`/`t` carry over from `M`.
- Round-trip on every Bicomodule constructed in `test/test_cofree.jl` and `test/test_kan_extensions.jl` — confirm `Bicomodule(bridge_diagram(M)) ≈ M` element-wise.
- Étale-leg property: for every position `i`, the outfacing-direction map of `pi` at `i` is bijective (validator).

### 1.3 Out of scope

- Symbolic bridge diagrams. If the carrier has `SymbolicSet` positions, error out with a v0.7 pointer; the symbolic version waits for multi-var Dirichlet (which is when we'll need it anyway).
- Minimal / canonical bridge diagrams. Different choices of `b` give isomorphic but not equal triples; we ship one canonical choice (the one read off from the carrier as-given) and document that other choices are equivalent up to iso.

---

## 2. `is_linear` / `is_conjunctive` predicates

**Paper.** Definition 6.4 + Corollaries 6.15 / 6.17. In the discrete-base setting, a bicomodule is *linear* iff its bridge diagram has `E = B` and `π = id` (Σ∆ form, ≃ left adjoint in Cat♯), and *conjunctive* iff `B = D` (Π∆ form, ≃ right adjoint). For non-discrete bases the same characterization works pointwise.

### 2.1 Proposed design

```julia
# src/CatSharp.jl

is_linear(M::Bicomodule) :: Bool
is_conjunctive(M::Bicomodule) :: Bool

# Wrapper types — opt-in, for callers that want the static guarantee
struct LinearBicomodule
    bicomodule::Bicomodule
    function LinearBicomodule(M::Bicomodule)
        is_linear(M) || error("LinearBicomodule: input bicomodule is not linear")
        new(M)
    end
end
struct ConjunctiveBicomodule
    bicomodule::Bicomodule
    function ConjunctiveBicomodule(M::Bicomodule)
        is_conjunctive(M) || error("ConjunctiveBicomodule: input bicomodule is not conjunctive")
        new(M)
    end
end
```

The predicates are thin wrappers over `bridge_diagram` — they inspect `s` and `pi`, no separate code path. The wrapper types exist so future operations (especially weak duality on multi-var, span ↔ linear) can dispatch.

### 2.2 Tests

- Identity bicomodule on `c` is *both* linear and conjunctive.
- `linear_bicomodule_from_span` (item #5) always returns linear bicomodules.
- `cofree_comonoid(p, depth)` gives a bicomodule that is *neither* in general (regression test, this is the obvious negative example).
- Composition lemma: composition of linear bicomodules is linear (Prop 6.16); same for conjunctive. Test on a few hand-built examples.

### 2.3 Out of scope

- Mixed bicomodules — neither linear nor conjunctive. Predicates just return `false`; we don't try to classify further.
- Dispatching `weak_dual` differently on `LinearBicomodule` vs `ConjunctiveBicomodule`. That dispatch lives in v0.7 alongside multi-var Dirichlet.

---

## 3. `weak_dual(p)` — single-variable Dirichlet weak dual

**Paper.** Example 7.2: `p^∨ := [p, y] = Σ_{f: Π p[i] → p(1)} y^{p(1)}`. The internal-hom `[p, q]` for the Dirichlet ⊗ on Poly is already implicitly available (we have `parallel` from Monoidal.jl:323 plus the closure machinery in Closure.jl); weak dual is just the `q = y` specialization, but it's worth a named operation because the reflexive objects (those with `p^{∨∨} ≅ p`) are exactly the linears `Ay` and representables `y^A` — useful symmetry to expose.

### 3.1 Proposed design

```julia
# src/Monoidal.jl  (extends existing)

weak_dual(p::AbstractPolynomial) :: Polynomial
# == [p, y] in (Poly, y, ⊗_Dir)

is_reflexive(p::AbstractPolynomial; depth::Int=2) :: Bool
# Test p^{∨∨} ≅ p element-wise; `depth` bounds materialization for symbolic p.
```

Implementation: positions of `p^∨` are functions `Π p[i] → p(1)` (so the positions form a finite/symbolic exponential set), each with direction-set `p(1)`. For finite `p`, this is an enumeration; for symbolic `p`, we lean on `SymbolicSet` exponentials added in v0.3.

**Naming.** `weak_dual` rather than `dual` because:
- The strong dual (full involution) only exists on the reflexive sub-class.
- The Niu/Spivak book uses ∨ notation for this specific construction; "weak" matches the paper's terminology.

### 3.2 Tests

- `weak_dual(y) == y`: representable is reflexive, dual of `y` is `y`.
- `weak_dual(Ay)` for a constant set: linear is reflexive — `weak_dual(weak_dual(Ay)) ≈ Ay` element-wise.
- `weak_dual(y^A)`: representable is reflexive — same round-trip.
- Generic polynomial `Σ y^{S_i}` with mixed exponents: `weak_dual^2 ≠ p` in general. Document and test.
- `is_reflexive` agrees with `weak_dual^2 ≈ p` on a battery of small polynomials.

### 3.3 Out of scope

- Multi-variable weak dual `[p, y]` in `d-Set[c]`. That's v0.7; it's the load-bearing operation behind Theorem 7.19's linear↔conjunctive equivalence.
- The full duoidality natural map `(p◁q)⊗(p'◁q') → (p⊗p')◁(q⊗q')` (Prop 7.10). Also v0.7.
- Strong-dual structure on the reflexive sub-category (a presentation as a `*-autonomous` category). Probably never; if a user needs this, the wrappers from #2 plus `weak_dual` are enough machinery.

---

## 4. List polynomial `u = Σ_{N∈ℕ} y^N` and `[u/u] ≅ Fin^op`

**Paper.** Definition 8.6: the polynomial `u := Σ_{N∈ℕ} y^N` has its comonoid structure giving `[u/u] ≅ Fin^op` (the skeleton of finite sets and functions, opposite). This is a building block — it appears in §8 as the carrier for aggregation, but it's also the cleanest worked example of an *infinite-positions* polynomial that the symbolic-positions infrastructure was designed to support, and a great test case for v0.7's multi-var Dirichlet.

### 4.1 Proposed design

```julia
# src/Demos.jl  (extends existing)

const LIST_POLYNOMIAL = let
    # u = Σ_{N ∈ ℕ} y^N
    Polynomial(
        positions = NaturalNumbers(),                  # symbolic ℕ
        directions_at = N -> FiniteSet(0:(N-1))        # at position N, direction set has size N
    )
end

list_polynomial() = LIST_POLYNOMIAL

# The comonoid structure on u, induced by the operad of sequence concatenation.
list_comonoid() :: Comonoid

# The coclosure [u/u], which is iso to Fin^op
list_self_coclosure() :: Polynomial
fin_op_skeleton() = list_self_coclosure()    # alias matching paper notation
```

The comonoid construction is essentially:
- Eraser `u → y`: at every position `N`, pick the unit of the empty sequence (well-defined because `0 ∈ ℕ`).
- Duplicator `u → u ◁ u`: position `N` maps to "split a sequence of length `N` into two sub-sequences", indexed by all `(N₁, N₂)` with `N₁ + N₂ = N` and a position chooser.

This needs the symbolic `NaturalNumbers` set to support `[u/u]` lazily — the coclosure has an infinite position set and shouldn't be enumerated.

### 4.2 Tests

- `list_polynomial()` validates as a polynomial (positions are a set, directions per position are a set).
- `list_comonoid()` passes `validate_comonoid` element-wise on positions `0`, `1`, `2`, `3`, `5`, `10`.
- `list_self_coclosure()` round-trips: for a small lens `f: u^? → u^?`, the corresponding morphism through `[u/u]` agrees on a few sample positions.
- Iso to `Fin^op`: `Fin^op` constructed via `free_labeled_transition_comonoid` on a small finite skeleton agrees with the truncation of `list_self_coclosure()` at depth 5.

### 4.3 Out of scope

- Continuous version `u_R = Σ_{r ∈ ℝ_≥0} y^{[0,r]}`. Different category.
- The full `[u^k / u^j]` machinery for the multi-arity list operad. Useful for §8 but only matters once aggregation lands.
- Performance pass on the symbolic-coclosure code path. If `list_self_coclosure()` is the slow operation that motivates an optimization, address it then; not now.

---

## 5. `linear_bicomodule_from_span` / `span_from_linear_bicomodule`

**Paper.** Corollary 6.17: `Span(Set) ≃ Cat♯_lin` as bicategories. Concretely, a span of finite sets `C ←ˢ S →ᵗ D` corresponds to the linear bicomodule `Cy ▷ Sy ◁ Dy` with carrier `Sy`, left coaction induced by `s`, right coaction induced by `t`. Composition of spans (pullback) corresponds to bicomodule composition.

### 5.1 Proposed design

```julia
# src/CatSharp.jl

struct Span
    apex::AbstractSet
    left_leg::Function     # apex → C
    right_leg::Function    # apex → D
    left_base::AbstractSet # C
    right_base::AbstractSet # D
end

linear_bicomodule_from_span(sp::Span) :: LinearBicomodule
span_from_linear_bicomodule(M::LinearBicomodule) :: Span

# Convenience: round-trippable composition
function compose(sp1::Span, sp2::Span)
    @assert sp1.right_base == sp2.left_base
    # Pullback construction
    ...
end
```

The conversion is mechanical:
- `linear_bicomodule_from_span`: take `Sy` as the carrier, `s`/`t` map directly to position-maps that determine the coactions. The right base is `discrete_comonoid(D)` (helper: discrete category on `D` as a comonoid in Poly).
- `span_from_linear_bicomodule`: read off `s` from the left coaction's position map, `t` from the right coaction's position map. The bridge diagram from #1 makes this trivial.

**Why this matters.** Today, building a "data migration along a span" bicomodule requires assembling positions, directions, and two coactions by hand. With #5, users hand us `(C, S, D, s, t)` and we hand them back a validated `LinearBicomodule`. This is the discrete-base sweet spot of the entire Cat♯ apparatus — the case most users will reach for first.

### 5.2 Tests

- Identity span on `C` round-trips to identity bicomodule on `discrete_comonoid(C)`.
- Span composition (pullback) agrees with bicomodule composition for several small spans.
- Linearity: `is_linear(linear_bicomodule_from_span(sp))` is always `true`.
- Demo: a join-style span `(R, R → A, R → B)` (a relation `R ⊆ A × B`) gives the bicomodule whose composition with another span is the relational join. Asserts a small concrete example.

### 5.3 Out of scope

- Spans of categories (non-discrete bases). The construction generalizes — that's what the paper actually states — but we ship the discrete case in v0.6 and lift to general categories when the multi-var Dirichlet machinery lands in v0.7. Document the planned generalization in the docstring.
- Spans-up-to-iso (the actual bicategorical hom). We treat spans as data, and equality is on-the-nose; users who need iso-classes can quotient themselves.
- Conjunctive analog `conjunctive_bicomodule_from_cospan`. Only useful once #2's `ConjunctiveBicomodule` is wired into more operations; deferred to v0.7.

---

## 6. Aggregation framework — separate library (PolyAggregation.jl)

> **Decision (proposed, 2026-05-03):** The aggregation framework from §8 of *Functorial Aggregation* lives in a separate package, **PolyAggregation.jl**, not Poly.jl core. Mirrors the 2026-05-02 PolyMarkov.jl decision: keeps Poly.jl free of database-instance machinery, commutative-monoid registries, and Fin → Set "aggregator functor" types that are only meaningful in the aggregation context. PolyAggregation.jl can ship on its own cadence and depend on Poly.jl ≥ v0.7 (when multi-var Dirichlet ⊗ is in core).

The design seed below is preserved here as the bridge from the v0.6 work to the PolyAggregation.jl repo. When that repo spins up, this section is moved into its `extensions_v1_design.md` and removed from here.

### 6.1 What aggregation looks like in Cat♯

A *schema* `(c, ↻)` consists of a small category `c` and, for each object `a ∈ Ob(c)`, an *aggregation functor* `↻_a : Fin → Set`. The standard family of aggregators comes from commutative monoids `M`: take `↻_a(N) := M^N` (compatible with restriction along functions `N → N'`).

An *instance* `(X, α)` over schema `(c, ↻)` consists of a finite-valued `c`-set `X : c → Fin` and, for each object `a`, an "aggregable value assignment" `α_a ∈ ↻_a(X(a))`.

**Theorem 8.8.** Aggregation is a homomorphism of left modules in `Cat♯_lin`:
```
↻^α : c(1)y ◁ c → c(1)y
```
realizing the universal property that GROUP BY is the right adjoint of querying along certain functors.

### 6.2 What PolyAggregation.jl needs from Poly.jl

| Needs | Available in Poly.jl version |
|---|---|
| `Bicomodule`, `Comonoid`, `Lens`, `compose` for ◁ | ✓ v0.5 (today) |
| `LinearBicomodule` wrapper + `is_linear` predicate | v0.6 (item #2) |
| List polynomial `u` and `[u/u] ≅ Fin^op` | v0.6 (item #4) |
| Span ↔ linear bicomodule dictionary | v0.6 (item #5) |
| **Multi-variable Dirichlet ⊗ on `d-Set[c]`** | **v0.7 (planned)** |
| **Module homomorphism types** (left modules in Cat♯_lin) | **v0.7 (planned)** |
| **Cat♯ left Kan extensions** (Prop 6.7, multi-var) | **v0.7 (planned)** |

The critical observation is that **PolyAggregation.jl cannot meaningfully start until v0.7 lands**. v0.6 is the scaffolding round; v0.7 is the round that unblocks the spinout.

### 6.3 What PolyAggregation.jl owns

```julia
# In PolyAggregation.jl

struct AggregationFunctor
    apply::Function          # N::Int -> Set  (functorial in N)
    restrict::Function       # (f::Function, N::Int, N'::Int) -> (apply(N) -> apply(N'))
end

# Built-ins
sum_aggregator(M::CommutativeMonoid) :: AggregationFunctor
count_aggregator() :: AggregationFunctor
list_aggregator() :: AggregationFunctor      # the universal one — `↻(N) = u`-shaped

struct Schema
    category::Comonoid                              # c
    aggregators::Dict{Position, AggregationFunctor} # ↻_a per object
end

struct Instance
    schema::Schema
    data::Function         # a -> FinSet,  the c-set X
    values::Dict{Position, Any}   # α_a ∈ ↻_a(X(a))
end

aggregate(inst::Instance) :: BicomoduleMorphism
# Builds the Theorem 8.8 module homomorphism via the universal construction
```

Worked examples it ships with: SQL-like GROUP BY on a small toy schema, sum-by-key, count-by-key, and a spec-vs-instance round trip showing schema migration commutes with aggregation in the cases the paper proves it does.

### 6.4 Boundary discipline

PolyAggregation.jl **does not** export polynomial constructors that don't exist in core. If a user wants a custom aggregator, they construct the underlying linear bicomodule with Poly.jl primitives and hand it over. This keeps the dependency arrow strictly one-way: **PolyAggregation.jl → Poly.jl**, never back.

### 6.5 Naming and repo layout

- Repo: `PolyAggregation.jl`, sibling of `PolyMarkov.jl`.
- Module name: `PolyAggregation`.
- Initial version: `v0.1.0` once Poly.jl v0.7 ships.
- Docs site: hangs off the same `polynomial.* ` Documenter domain (or whichever pattern PolyMarkov ends up using; align with that).

---

## 7. Open questions

### Item #1 — bridge diagrams

**Q1.1** — Should `BridgeDiagram` carry the original `Bicomodule` reference (as drafted), or be a standalone struct that round-trips? *Recommendation:* carry the reference. Round-trip is a function `Bicomodule(::BridgeDiagram)` that re-uses the data. Makes round-trip tests cheap and lets users introspect without losing the source.

**Q1.2** — Where does `BridgeDiagram` live? `src/CatSharp.jl` (new file) or extend `src/Cofree.jl`? *Recommendation:* new file `src/CatSharp.jl`. Cofree.jl is already 3700+ lines; this is a natural seam.

**Q1.3** — Étale-leg validator: run automatically inside the `BridgeDiagram` constructor, or expose as `validate_bridge_diagram(::BridgeDiagram)`? *Recommendation:* both — constructor runs it on-by-default (`validate=true` keyword), validator exposed for re-use.

### Item #2 — linear / conjunctive

**Q2.1** — Wrapper types `LinearBicomodule` / `ConjunctiveBicomodule`: ship with v0.6, or wait until v0.7 actually dispatches on them? *Recommendation:* ship with v0.6. Trivial code, gives downstream users (especially PolyAggregation.jl) the type to dispatch on starting day-one.

**Q2.2** — Should `LinearBicomodule(M)` *normalize* `M` to its bridge-diagram form, or just validate and wrap? *Recommendation:* validate and wrap; never mutate the carrier. Normalization is a separate `normalize_linear` function if anyone asks.

### Item #3 — weak dual

**Q3.1** — Name. `weak_dual` (paper) vs `dual` (shorter, but ambiguous with the strong dual which we don't have) vs `dirichlet_dual` (specific but verbose). *Recommendation:* `weak_dual`. Match the paper. Document the `^∨` correspondence in the docstring.

**Q3.2** — `is_reflexive(p; depth)` default depth: `2` (one round-trip) or `3` (catches subtler counterexamples)? *Recommendation:* `2`. Cheap, sufficient for the linear / representable cases that are actually reflexive.

### Item #4 — list polynomial

**Q4.1** — Where does `LIST_POLYNOMIAL` live? `Demos.jl` (current home of named examples) or a new `src/Examples.jl`? *Recommendation:* `Demos.jl`, alongside the existing named polynomials. Tag with an `# aggregation building block` comment so future readers grep find it.

**Q4.2** — Should we also ship the Kleisli triple `(u, η, μ)` showing `u` is the free-monoid monad on Set? Useful for the comonoid construction and for §8 prep, but it's a chunk of code on its own. *Recommendation:* yes — the comonoid construction needs it internally, and exposing it costs almost nothing extra. Adds maybe 30 lines.

### Item #5 — span ↔ linear bicomodule

**Q5.1** — `Span` struct vs Catlab's `FreeBicategoryOfRelations` / `Spans` machinery. Catlab has spans of FinSets; do we adopt those? *Recommendation:* ship our own thin `Span` struct in v0.6 to avoid pulling Catlab into the dependency footprint of this PR; revisit interop with Catlab in v0.7 once we know whether multi-var Dirichlet uses any other Catlab types.

**Q5.2** — Pullback computation in `compose(::Span, ::Span)`: hand-roll, or delegate to Catlab's `pullback`? *Recommendation:* hand-roll for finite sets (10 lines). Catlab interop is a separate decision.

**Q5.3** — Should `linear_bicomodule_from_span` accept *just* the apex + two legs (assuming bases are inferred from leg codomains), or require explicit bases? *Recommendation:* both — primary constructor takes explicit bases; convenience constructor `linear_bicomodule_from_span(apex, s, t)` infers bases from `image(s)` / `image(t)`.

### Cross-cutting

**Q6.1** — `src/CatSharp.jl` as a new file: any concerns about module structure? Should items #1, #2, #5 all go there, or split (#1/#2 in `Cofree.jl` extension, #5 in a `Span.jl`)? *Recommendation:* one new file `src/CatSharp.jl` housing #1 + #2 + #5. They're all "Cat♯ inspection / discrete-base operations." Weak dual (#3) stays in Monoidal.jl, list polynomial (#4) stays in Demos.jl.

**Q6.2** — PolyAggregation.jl spinout: do we lock in the name and reserve the GitHub repo now (so it shows up in search results next to PolyMarkov.jl)? *Recommendation:* yes, reserve the name; create an empty repo with a README that says "scaffolding-in-progress, depends on Poly.jl v0.7+". Costs nothing, prevents a name collision.

**Q6.3** — Should v0.6 docs include a "what the v4 design doc *doesn't* implement" callout linking forward to v0.7 (multi-var Dirichlet) and PolyAggregation.jl? *Recommendation:* yes. One paragraph in the v0.6 release notes. Helps anyone reading the paper alongside the library understand the gap.

---

## 8. Phasing / release plan

v0.6 ships #1 → #2 → #3 → #4 → #5 in that order. PR ordering rationale:

1. **#1 first** because #2 and #5 both depend on it, and it's the most novel piece (introspection of any existing `Bicomodule`). Lands the new `src/CatSharp.jl` file.
2. **#2 next** — trivially small, but unblocks #5's wrapper return type.
3. **#3 in parallel** — independent of #1, #2; can land any time after the symbolic-positions story is confirmed solid.
4. **#4** — independent, but better to land after #3 because it's the first user of `weak_dual` in a worked example (the `[u/u]` derivation can verify reflexivity sanity-checks).
5. **#5** — last; needs #1 and #2.

Estimated effort: ~2 weeks for #1, ~1 day each for #2/#3/#4, ~3-4 days for #5. Total: 3 weeks of focused work.

**Handoff to PolyAggregation.jl.** Bridge doc already drafted at `docs/dev/polyaggregation_handoff.md` (2026-05-03). Covers: what's in core (v0.5 + v0.6 + v0.7 capabilities PolyAggregation.jl can rely on), the §8 design seed expanded with `AggregationFunctor` / `Schema` / `Instance` / `aggregate` API, paper-section implementation status, and interface contracts (which types cross the boundary, which never do, type-piracy rules). The bridge doc travels *with* the PolyAggregation.jl repo when it spins up — at that point it becomes the first thing in `docs/dev/` over there, and §6 of this doc shrinks to a one-line pointer.

A sibling bridge doc — `docs/dev/polymarkov_handoff.md` — applies the same template to PolyMarkov.jl, capturing the architectural difference between the two satellites (Markov is a Kleisli twist on the morphism layer, ready to spin up nearly today; Aggregation is a universal-construction application, gated on v0.7 multi-var Dirichlet).

**v0.7 preview.** The v0.7 design doc will cover: multi-variable Dirichlet ⊗ on `d-Set[c]` (paper §7.2-7.3, Lemma 7.13, Cor 7.15); the contravariant equivalence `Cat♯_lin ↔ Cat♯_disc,con` (Theorem 7.19); profunctor ↔ conjunctive bicomodule dictionary (§7.3.1, Prop 7.25); generalization of `kan_along_bicomodule` to general (c,d) (Prop 6.7); and the duoidality natural map (Prop 7.10, 7.17).

---

## 9. Out of scope for v0.6

- **Multi-variable Dirichlet ⊗** on `d-Set[c]` — v0.7. Single-var ⊗ (`parallel`) stays as-is.
- **Cat♯ left Kan extensions** for general `(c,d)` (Prop 6.7) — v0.7. `kan_along_bicomodule` and `kan_2cat` handle the cases we have today.
- **Profunctor ↔ conjunctive bicomodule** dictionary (§7.3.1) — v0.7. Catlab interop story to be settled then.
- **Theorem 7.19 weak duality between Cat♯_lin and Cat♯_disc,con** — v0.7, gated on multi-var Dirichlet.
- **Duoidality (◁, ⊗)** (Prop 7.10, 7.17) — v0.7.
- **Aggregation framework** (paper §8) — moved to PolyAggregation.jl, depends on v0.7.
- **Continuous / measure-theoretic versions** of `u`, weak dual, or anything else — out of scope, possibly forever.
- **Niu/Spivak Chapter 5 / Sprint 9** — still skipped per 2026-04-27 call.
- **PolyViz Luxor → Makie/GraphMakie/TikzPictures rewrite** — still on the standing todo, separate effort.
- **Catlab.jl deeper integration** — same.
- **Performance pass on Sprint 8 tree enumeration** — same.
- **Markov polynomials in any form** — lives in PolyMarkov.jl.
