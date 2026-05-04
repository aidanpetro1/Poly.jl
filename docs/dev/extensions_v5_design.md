# Poly.jl — Extensions v5 Design Doc (v0.5.1 PolyAggregation Minimum-Surface Patch)

> **Status**: SIGNED OFF, 2026-05-03. All open questions resolved in the same session — see `extensions_v4_design.md` §7 for the v0.6 Q list and the resolution log in memory (`project_poly_v051_v06_resolved.md`). Implementation can start.

---

## 0. Summary

Five additive items that together form the **minimum surface** Poly.jl needs to expose so PolyAggregation.jl v0.1.x can drop its stubs and ship a working data-level `aggregate(::Instance)`. Designed as a patch release on top of the current shipping v0.5; no breaking changes; no new dependencies.

| # | Item | File | Lines (est.) | Days | Risk |
|---|---|---|---|---|---|
| 1 | `list_polynomial(; max_size=nothing)` — Def 8.6 | `src/Demos.jl` | ~80 | 0.5 | low |
| 2 | `is_linear(B)` + `LinearBicomodule(B)` — Def 6.4 | new `src/CatSharp.jl` | ~60 | 0.5 | low |
| 3 | `linear_bicomodule_from_span(C, D, S, s, t)` — Cor 6.17 (forward only) | `src/CatSharp.jl` | ~120 | 1.5 | medium |
| 4 | `c_one_y(c::Comonoid)` — Theorem 8.8 carrier | `src/CatSharp.jl` | ~30 | 0.25 | low |
| 5 | `morphisms_out_of(c, a)` + `cod_in_comonoid(c, a, f)` — comonoid ergonomics | `src/Comonoid.jl` | ~40 | 0.25 | low |
| — | Tests + docstrings + CHANGELOG | — | ~150 | 1 | — |
| — | **Total** | — | **~480** | **~4** | — |

**Source.** Items #1–#3 come from Spivak/Garner/Fairbanks, *Functorial Aggregation* (arXiv 2111.10968v7). Item #4 is a convenience for the carrier appearing at both ends of Theorem 8.8. Item #5 is pure ergonomics — wrappers around APIs PolyAggregation needs but that read awkwardly without dedicated names.

**Phasing.** This patch ships **only** the items above. The remainder of the original v0.6 Cat♯ inspection + duality bundle (`bridge_diagram`, `weak_dual` + `is_reflexive`, `ConjunctiveBicomodule` + `is_conjunctive`, the Kleisli triple `(u, η, μ)`, `span_from_linear_bicomodule` + `Span` struct + pullback) ships in **v0.6**, after this patch lands. Multi-variable Dirichlet ⊗ and Theorem 8.8's full categorical realization land in v0.7. PolyAggregation.jl v0.2.0 only requires this v0.5.1 patch; v0.3.0 will gate on v0.7. See `docs/dev/ROADMAP.md` for the cross-version picture.

**Where the codebase stands today.** v0.5 shipped `validate_retrofunctor_forward` for partial-image retrofunctors. We have `Bicomodule` with `left_base`/`right_base`/`left_coaction`/`right_coaction` (`src/Cofree.jl`), `regular_bicomodule(c)`, `Comonoid` with `eraser`/`duplicator`, `Lens` and `AbstractLens`, `parallel` for single-var Dirichlet ⊗, `kan_along_bicomodule`. No `is_linear`, no list polynomial, no span↔bicomodule dictionary. PolyAggregation.jl currently scaffolds `Schema`, `Instance`, `validate_instance`, the standard `AggregationFunctor` family, and four worked-example skeletons against v0.5 — but `aggregate(inst)` itself is stubbed pending v0.5.1.

---

## 1. `list_polynomial(; max_size=nothing)` — Def 8.6

**Paper.** Definition 8.6: the polynomial `u := Σ_{N ∈ ℕ} y^N` is the carrier of the universal aggregator; the comonoid structure on it gives `[u/u] ≅ Fin^op`. v0.5.1 ships only the polynomial; the comonoid + Kleisli triple `(u, η, μ)` ship in v0.6.

### 1.1 Public API

```julia
# src/Demos.jl  (extends existing)

# aggregation building block — used by PolyAggregation.jl's universal aggregator
"""
    list_polynomial(; max_size::Union{Int,Nothing}=nothing) -> AbstractPolynomial

The list polynomial `u = Σ_{N ∈ ℕ} y^N` of Spivak/Garner/Fairbanks Def 8.6 —
the universal "collect-into-a-list" polynomial.

- Without `max_size`: returns a polynomial whose `positions` is `NaturalNumbers()`
  and `direction_at(N)` is a finite set of size `N`. Cardinality of positions
  is `CountablyInfinite()`. Use this form for symbolic / lazy / infinite-N
  reasoning.

- With `max_size = K`: returns a finite truncation `Σ_{N=0..K} y^N` whose
  positions is `FinPolySet(0:K)`, suitable for finite enumeration and tests.

The Kleisli triple `(u, η, μ)` exhibiting `u` as the free-monoid monad on Set
will ship in v0.6 alongside `comonoid_from_list_polynomial`.

# Examples
```julia
u = list_polynomial()                          # Σ_{N ∈ ℕ} y^N (symbolic positions)
u_fin = list_polynomial(max_size=5)            # Σ_{N=0..5} y^N
direction_at(u_fin, 3) == FinPolySet([1,2,3])  # true
```
"""
function list_polynomial(; max_size::Union{Int,Nothing}=nothing) end
```

### 1.2 Semantics

- **Positions** = `NaturalNumbers()` (a symbolic set with cardinality `CountablyInfinite()`) when `max_size === nothing`, or `FinPolySet(0:K)` when `max_size = K`. Interpreted as "list lengths".
- **Direction-at-N** = `FinPolySet(1:N)` — the `N` row indices. For `N == 0`, returns `FinPolySet(Int[])` (empty).
- **No comonoid structure in v0.5.1.** Just the polynomial. The natural comonoid (counit + concatenation duplicator) lands in v0.6 as `comonoid_from_list_polynomial`; the `[u/u] ≅ Fin^op` correspondence ships then too.

### 1.3 Tests

```julia
@testset "list_polynomial" begin
    # finite truncation
    u = list_polynomial(max_size=5)
    @test u isa AbstractPolynomial
    @test cardinality(positions(u)) == Finite(6)        # {0, 1, 2, 3, 4, 5}
    @test cardinality(direction_at(u, 0)) == Finite(0)
    @test cardinality(direction_at(u, 3)) == Finite(3)
    @test direction_at(u, 3) == FinPolySet([1, 2, 3])

    # infinite default
    u_inf = list_polynomial()
    @test cardinality(positions(u_inf)) == CountablyInfinite()
    @test cardinality(direction_at(u_inf, 7)) == Finite(7)
end
```

### 1.4 Why now / out of scope

PolyAggregation's `list_aggregator()` is the universal aggregator (`examples/list_universal.jl` already demonstrates this at the data level). With `list_polynomial()` available, `list_aggregator` can be documented as the aggregator whose carrier is `list_polynomial()`, closing the data-vs-polynomial gap. It's also a clean test case for the symbolic-positions code path added in v0.3.

Out of scope for v0.5.1: the Kleisli triple `(u, η, μ)`, the `[u/u] ≅ Fin^op` isomorphism, the continuous-list analog `u_R = Σ_{r ∈ ℝ_≥0} y^{[0,r]}`. All v0.6+ unless otherwise marked.

---

## 2. `is_linear(B)` + `LinearBicomodule(B)` — Def 6.4

**Paper.** Definition 6.4 + Corollary 6.17. A bicomodule is *linear* iff its bridge diagram has `E = B` and `π = id` — equivalently (in the discrete-base case), iff its carrier is `Sy` for some position-set `S` (every position has direction-set of size exactly 1). Linearity is the predicate that lets PolyAggregation dispatch span-shaped queries onto a `LinearBicomodule` cleanly.

### 2.1 Public API

```julia
# src/CatSharp.jl  (NEW FILE)

"""
    is_linear(B::Bicomodule) -> Bool

Predicate: does `B` factor as `Σ_t ∘ Δ_s` for some span `(s, t)` of finite
sets, with no `Π` step? Equivalently: is the carrier of `B` of the form `Sy`
for some position-set `S` — every position has direction-set of size exactly
one. Equivalently (Cor 6.17): is `B` a left adjoint in Cat♯?

This predicate is structural: it inspects `direction_at(B.carrier, i)` for
every `i` (or runs symbolically when positions are infinite). It does NOT
attempt to construct a bridge diagram — that's `bridge_diagram(B)`, v0.6.
"""
function is_linear(B::Bicomodule) end

"""
    LinearBicomodule(B::Bicomodule)

Typed wrapper asserting `is_linear(B)`. Construction errors if `B` is not
linear. Use this when you want type-level guarantees for downstream
operations that require the linear case (e.g. PolyAggregation's
`aggregate_along` query, which is morally a span GROUP BY).

`LinearBicomodule` does NOT mutate or normalize the underlying bicomodule —
it is a pure tag. Existing operations on `Bicomodule` lift through
`.underlying`.
"""
struct LinearBicomodule
    underlying::Bicomodule
    function LinearBicomodule(B::Bicomodule)
        is_linear(B) || error("LinearBicomodule: B is not linear")
        new(B)
    end
end
```

### 2.2 Semantics

`is_linear(B)`:
1. If `cardinality(positions(B.carrier))` is finite, iterate every position and check `cardinality(direction_at(B.carrier, i)) == Finite(1)`. Return `false` on first violation.
2. If positions are symbolic (e.g. `NaturalNumbers()`), look for a witness via the carrier's symbolic shape: `Sy` written as `linear(positions(...))` is recognized structurally; otherwise `is_linear` returns `false` conservatively (and emits a single-line `@info` noting the symbolic case is not exhaustively checked, with a v0.6 forward-pointer to `bridge_diagram`).

`LinearBicomodule(B)`:
- Validate-and-wrap, never mutate. Stores `B` unchanged in `.underlying`.
- All `Bicomodule` operations (`compose`, `validate_bicomodule`, etc.) work on `.underlying` — this v0.5.1 patch does not lift any methods to dispatch on `LinearBicomodule` directly. PolyAggregation.jl is the first dispatch consumer; its v0.2.0 will define methods on `::LinearBicomodule` from outside.

### 2.3 Tests

```julia
@testset "is_linear / LinearBicomodule" begin
    # Discrete comonoid → its regular bicomodule has a linear carrier
    c = discrete_comonoid(FinPolySet([:a, :b]))
    B = regular_bicomodule(c)
    @test is_linear(B)
    L = LinearBicomodule(B)
    @test L.underlying === B

    # State-system comonoid → the regular bicomodule's carrier is NOT linear
    cs = state_system_comonoid(FinPolySet([:s, :t]),
                               FinPolySet([:in]),
                               (s, x) -> :t,
                               FinPolySet([:out]))
    Bns = regular_bicomodule(cs)
    @test !is_linear(Bns)
    @test_throws ErrorException LinearBicomodule(Bns)
end
```

### 2.4 Why now / out of scope

`aggregate_morphism(::Instance)` returns a homomorphism between linear bicomodules. PolyAggregation needs a way to say "this argument has to be linear" at the type level so the construction doesn't accept arbitrary bicomodules and produce nonsense. Without `LinearBicomodule`, every PolyAggregation function takes `::Bicomodule` and runs `is_linear` at the boundary by hand.

Out of scope for v0.5.1: `is_conjunctive` + `ConjunctiveBicomodule` (v0.6, symmetric structure), bridge-diagram-based linearity inspection (v0.6), method dispatch ON `::LinearBicomodule` for any core operation (no current consumer; PolyAggregation will dispatch from outside).

---

## 3. `linear_bicomodule_from_span(C, D, S, s, t)` — Cor 6.17 (forward only)

**Paper.** Corollary 6.17: `Span(Set) ≃ Cat♯_lin` as bicategories. Concretely, a span `Ob(C) ←ˢ S →ᵗ Ob(D)` between the object-sets of two comonoids corresponds to the linear bicomodule `Cy ▷ Sy ◁ Dy` with carrier `Sy`. **v0.5.1 ships only the forward direction** (span → bicomodule). The reverse direction `span_from_linear_bicomodule` and a dedicated `Span` struct ship in v0.6.

### 3.1 Public API

```julia
# src/CatSharp.jl  (extends)

"""
    linear_bicomodule_from_span(
        C::Comonoid, D::Comonoid, S::FinPolySet,
        s::Function, t::Function;
        validate::Bool=true,
    ) -> LinearBicomodule

Build the linear bicomodule `Cy ▷ Sy ◁ Dy` corresponding to a span
`Ob(C) ←^s S →^t Ob(D)` between the object-sets of two comonoids
(viewed as discrete categories on the object level for v0.5.1; non-discrete
bases generalize and ship in v0.6 via `span_from_linear_bicomodule`).

Cor 6.17 of Spivak/Garner/Fairbanks: `Span(Set) ≃ Cat♯_lin` as bicategories;
this constructor is one direction of that equivalence.

- `s :: Function`: maps each `x ∈ S` to a position of `C.carrier`.
- `t :: Function`: maps each `x ∈ S` to a position of `D.carrier`.
- `validate=true`: check `s(x) ∈ Ob(C)` and `t(x) ∈ Ob(D)` for every `x ∈ S`.
  Pass `false` to skip when constructing in tight loops.

# Example
```julia
C = discrete_comonoid(FinPolySet([:customer]))
D = discrete_comonoid(FinPolySet([:order]))
S = FinPolySet([:o1, :o2, :o3])
B = linear_bicomodule_from_span(C, D, S,
        x -> :customer,           # s : S → Ob(C)
        x -> :order)              # t : S → Ob(D)
```

The reverse direction (`span_from_linear_bicomodule`), the `Span` struct, and
the convenience constructor `linear_bicomodule_from_span(span)` ship in v0.6.
"""
function linear_bicomodule_from_span(C::Comonoid, D::Comonoid, S::FinPolySet,
                                     s::Function, t::Function;
                                     validate::Bool=true) end
```

### 3.2 Semantics

The carrier of the result is `linear(S)` (i.e., `Sy` — every `x ∈ S` is a position with single direction). Coactions are read off the span:

- **Left coaction `Sy → Cy ▷ Sy`:** at position `x ∈ S`, return `(s(x), b ↦ x)`. Here `b` ranges over `direction_at(C.carrier, s(x))` — for `discrete_comonoid` that's only the identity, so the closure is constant `x`. For non-discrete `C`, the construction extends each `x` with the trivial action on out-morphisms (every morphism `f : s(x) → s(x)'` of `C` factors trivially through `x`).
- **Right coaction `Sy → Sy ▷ Dy`:** at position `x ∈ S`, return `(x, e ↦ t(x))` symmetrically.

`validate=true` walks `S` once and asserts `s(x) ∈ positions(C.carrier)` and `t(x) ∈ positions(D.carrier)`. The constructor ends with `LinearBicomodule(B)` so a successful return always has `is_linear` witness.

### 3.3 Tests

```julia
@testset "linear_bicomodule_from_span" begin
    C = discrete_comonoid(FinPolySet([:c1, :c2]))
    D = discrete_comonoid(FinPolySet([:d1, :d2, :d3]))
    S = FinPolySet([:s1, :s2, :s3, :s4])

    # span: s1,s2 -> c1; s3,s4 -> c2; s1,s3 -> d1; s2 -> d2; s4 -> d3
    sf = x -> x in (:s1, :s2) ? :c1 : :c2
    tf = x -> x === :s1 ? :d1 :
              x === :s2 ? :d2 :
              x === :s3 ? :d1 : :d3

    L = linear_bicomodule_from_span(C, D, S, sf, tf)
    @test L isa LinearBicomodule
    @test validate_bicomodule(L.underlying)
    @test positions(L.underlying.carrier) == S
    @test is_linear(L.underlying)

    # Validation rejects bad spans
    @test_throws ErrorException linear_bicomodule_from_span(
        C, D, S, x -> :nope, tf)
end
```

### 3.4 Why now / out of scope

PolyAggregation's `aggregate_along(inst, query::LinearBicomodule)` takes its query argument as a span, semantically. Today, users would have to construct the bicomodule by hand. With `linear_bicomodule_from_span`, the natural input form ("here's a span: source set, target set, two functions") is a one-liner.

Out of scope for v0.5.1: the reverse direction `span_from_linear_bicomodule`, the dedicated `Span{A,B}` struct, the pullback in `compose(::Span, ::Span)`, the convenience constructor `linear_bicomodule_from_span(span)` that infers bases from leg images. All v0.6.

Spans of categories (non-discrete bases) — the construction generalizes per the paper; we ship the discrete case here and lift to general categories when multi-var Dirichlet lands in v0.7.

---

## 4. `c_one_y(c::Comonoid)` — Theorem 8.8 carrier

**Paper.** §8.1: Theorem 8.8 realizes aggregation as a homomorphism `↻^α : c(1)y ◁ c → c(1)y` of left modules in `Cat♯_lin`. Both source and target use the bicomodule `c(1)y`. v0.5.1 ships this as a named convenience because every aggregation call site otherwise builds `c(1)y` with a 6-line literal.

### 4.1 Public API

```julia
# src/CatSharp.jl  (extends)

"""
    c_one_y(c::Comonoid) -> LinearBicomodule

The linear bicomodule `c(1)y` (carrier `linear(positions(c.carrier))`,
i.e., `Ob(c)·y`), viewed as a self-bicomodule `c ▷ c(1)y ◁ c`. Both
coactions go through the comonoid's eraser: each object-position maps
to itself, and morphisms-of-`c` act trivially (only identities pass through).

This is the standard "objects-only-linear" bicomodule that appears at
both ends of Theorem 8.8: the homomorphism is `c(1)y ◁ c → c(1)y`.

Equivalent to:
    linear_bicomodule_from_span(c, c, positions(c.carrier),
                                identity, identity)
…with the coaction shapes specialized to use `c`'s own structure on each
side.
"""
function c_one_y(c::Comonoid) end
```

### 4.2 Semantics

`c_one_y(c)` returns `LinearBicomodule(B)` where `B` has:
- `left_base = right_base = c`
- `carrier = linear(positions(c.carrier))` — one position per object of `c`, each with single direction.
- Both coactions: at position `a ∈ Ob(c)`, the coaction returns `(a, _ -> a)` after walking through `c.eraser` on the directions side. (Net effect: morphisms of `c` are forgotten; only object-tags propagate.)

The implementation is essentially a one-line wrapper around `linear_bicomodule_from_span` with `S = positions(c.carrier)` and `s = t = identity`, but factored out because:
1. The named function communicates intent — "the c(1)y carrier" is a paper concept worth surfacing.
2. PolyAggregation calls it dozens of times across schema/instance code paths; one named function is cheaper to read than `linear_bicomodule_from_span(c, c, positions(c.carrier), identity, identity)`.

### 4.3 Tests

```julia
@testset "c_one_y" begin
    c = free_labeled_transition_comonoid([:a, :b], [(:a, :f, :b)])
    L = c_one_y(c)
    @test L isa LinearBicomodule
    @test validate_bicomodule(L.underlying)
    @test positions(L.underlying.carrier).elements == [:a, :b]
    @test is_linear(L.underlying)

    # Round-trip via linear_bicomodule_from_span gives the same shape
    L2 = linear_bicomodule_from_span(c, c, positions(c.carrier),
                                     identity, identity)
    @test positions(L.underlying.carrier) == positions(L2.underlying.carrier)
end
```

### 4.4 Why now / out of scope

Theorem 8.8's source and target both use `c(1)y`. PolyAggregation v0.2.0 calls it as the carrier for `aggregate_morphism(::Instance)`. Without the convenience, every PolyAggregation call site that needs to talk about `c(1)y` builds it with a 6-line `Bicomodule(...)` literal.

Out of scope for v0.5.1: the dual `c(1)`-shaped object (would be `[c(1)y, y]`, gated on `weak_dual` in v0.6), conjunctive analog `c(1)y_con` (gated on `ConjunctiveBicomodule` in v0.6), generalization to `c(N)y` for `N > 1` (no current consumer).

---

## 5. `morphisms_out_of(c, a)` + `cod_in_comonoid(c, a, f)` — comonoid ergonomics

**Paper.** No specific section — these are pure ergonomics around the existing comonoid representation. PolyAggregation's `aggregate(inst)` walks the morphisms of `c` and applies aggregator restrictions along each; the walk needs to enumerate "morphisms out of `a`" and read codomains. Today the call is `direction_at(c.carrier, a)` — readable inside Poly.jl, opaque outside.

### 5.1 Public API

```julia
# src/Comonoid.jl  (extends)

"""
    morphisms_out_of(c::Comonoid, a) -> Vector

The list of all morphisms `f` of `c` with `dom(f) == a`, including the
identity. Each morphism is returned in the same shape as `c[a]`'s elements
(i.e., as direction-positions of the carrier).

Equivalent to `to_category(c).morphisms` filtered by `dom == a`, but without
forcing the full category enumeration when only the out-set at one object
is needed. The body is a thin wrapper over `direction_at(c.carrier, a)`.
"""
function morphisms_out_of(c::Comonoid, a) end

"""
    cod_in_comonoid(c::Comonoid, a, f) -> Object

For a morphism `f ∈ c[a]`, return its codomain (an object of `c`).
Equivalent to reading off `c.duplicator.on_positions.f(a)` and projecting
the codomain, which is the standard read but currently requires knowing
the duplicator's tuple shape.

Errors if `f ∉ direction_at(c.carrier, a)`.
"""
function cod_in_comonoid(c::Comonoid, a, f) end
```

### 5.2 Semantics

- `morphisms_out_of(c, a)` = `collect(direction_at(c.carrier, a))`. ~5 lines including the docstring.
- `cod_in_comonoid(c, a, f)`: reads `c.duplicator.on_positions(a)` (which returns `(a, f-action)` per `Comonoid` invariant) and projects the second component to its codomain via the existing duplicator-projection helper. Errors with a clear message if `f` is not in the out-set at `a`.

Both wrappers are pure renames of existing API; they exist for discoverability when the caller is thinking in *categorical* terms ("morphisms out of `a`", "codomain of `f`") rather than *polynomial* terms ("directions at position `a`", "duplicator's on-positions image").

### 5.3 Tests

```julia
@testset "morphisms_out_of / cod_in_comonoid" begin
    c = free_labeled_transition_comonoid([:a, :b], [(:a, :f, :b)])
    out_a = morphisms_out_of(c, :a)
    @test length(out_a) == 2          # identity + f
    @test cod_in_comonoid(c, :a, (:a, ())) == :a       # identity at :a
    @test cod_in_comonoid(c, :a, (:a, (:f,))) == :b    # f : a → b

    # Errors when f is not a morphism out of a
    @test_throws ErrorException cod_in_comonoid(c, :a, (:b, ()))
end
```

### 5.4 Why now / out of scope

PolyAggregation's `aggregate(inst)` walks the morphisms of `c` and applies aggregator restrictions along each. The natural call inside the walk is `morphisms_out_of(schema.category, a)` for each object `a`, then `cod_in_comonoid(c, a, f)` to read the target. With these wrappers, the walk reads as a 5-line categorical loop; without them, it reads as `direction_at`/`duplicator.on_positions` plumbing.

Out of scope for v0.5.1: `morphisms_into(c, b)` (symmetric — uncommon in aggregation, deferred until a consumer asks), `compose_in_comonoid(c, f, g)` (already covered by `c.duplicator`'s composition; named version only if a consumer asks).

---

## 6. Cross-cutting concerns

### 6.1 Module structure

- **New file: `src/CatSharp.jl`** for items #2, #3, #4. v0.6 will extend the same file with `bridge_diagram`, `is_conjunctive` + `ConjunctiveBicomodule`, `span_from_linear_bicomodule` + `Span` + pullback. PolyAggregation.jl can rely on `using Poly: is_linear, LinearBicomodule, linear_bicomodule_from_span, c_one_y` from a stable import path.
- **Extension: `src/Demos.jl`** for item #1 — `list_polynomial` lives alongside other named polynomials with a `# aggregation building block` comment for grep.
- **Extension: `src/Comonoid.jl`** for item #5 — `morphisms_out_of` and `cod_in_comonoid` live next to the existing accessor APIs.

`src/Cofree.jl` is unchanged by v0.5.1.

### 6.2 Backward compatibility

All five items are additive. No changes to existing exports, signatures, or behavior. The new file `src/CatSharp.jl` gets `include`d from the top-level module file; `LinearBicomodule` and `is_linear` are re-exported; `linear_bicomodule_from_span`, `c_one_y` are exported. `morphisms_out_of`, `cod_in_comonoid`, `list_polynomial` are exported from their respective modules.

### 6.3 PolyAggregation.jl repo

Repo placeholder is **deferred** until v0.5.1 ships and PolyAggregation has scaffold code to push. No empty placeholder repo on GitHub now.

### 6.4 CHANGELOG framing

v0.5.1's CHANGELOG entry headline: **"Minimum surface for PolyAggregation.jl v0.1.x."** Body lists the five items with one-paragraph forward-pointer naming v0.6's items (`bridge_diagram`, `weak_dual`, `ConjunctiveBicomodule`, reverse-span/Span machinery, Kleisli triple) and v0.7's gating items (multi-variable Dirichlet ⊗, Theorem 7.19 weak duality, profunctor↔conjunctive bicomodule). This is the public-facing "what's coming" paragraph; the design specifics live here in `extensions_v5_design.md` and the v0.6 picture in `extensions_v4_design.md`.

### 6.5 Open question for PolyAggregation (NOT for Poly.jl)

PolyAggregation's `Instance` currently stores `data :: object → FinPolySet` but doesn't carry the morphism action `X(f) : X(a) → X(b)` for non-identity `f`. Without that, `aggregate(inst)` has no source-to-target row mapping to apply `aggregator.restrict` along. Two PolyAggregation-side candidate fixes:

1. Add an `Instance.transitions :: Dict{Morphism, Function}` field. *Pro:* explicit, matches the §8.1 setup verbatim. *Con:* morphism keys are awkward, functoriality validation at construction time is non-trivial.
2. Replace `Instance.data` with a `Poly.LeftComodule` (or `RightComodule` — variance TBD) over the schema's `Comonoid`. The c-set `X`'s morphism action falls out of the comodule's coaction. *Pro:* typed and validated by Poly.jl already (`regular_left_comodule`, `validate_left_comodule`). *Con:* requires PolyAggregation users to know what a comodule is, or for PolyAggregation to ship a high-level constructor that hides it.

This is a PolyAggregation-side decision (see `polyaggregation_handoff.md` §6). The v0.5.1 patch doesn't need to take a position; it just keeps the existing comodule constructors usable.

---

## 7. Implementation order

PolyAggregation's order works nearly as-is, with one tweak — `c_one_y` and `morphisms_out_of` are independent of the cluster and can land first as warm-up:

1. **`morphisms_out_of` + `cod_in_comonoid`** (~0.25 day) — pure Comonoid.jl ergonomics, no dependencies. PR #1.
2. **`list_polynomial(; max_size)`** (~0.5 day) — Demos.jl, isolated. PR #2.
3. **`is_linear` + `LinearBicomodule`** (~0.5 day) — first chunk of new CatSharp.jl. PR #3.
4. **`linear_bicomodule_from_span`** (~1.5 days) — depends on (3). PR #4.
5. **`c_one_y`** (~0.25 day) — depends on (4); one-line wrapper around `linear_bicomodule_from_span`. PR #5.
6. **Tests + docstrings + CHANGELOG** (~1 day) — folded into the PRs above; this line is the buffer for cross-cutting docs polish. PR #6.

Total: ~4 days. No critical path beyond the (3) → (4) → (5) chain.

---

## 8. Out of scope for v0.5.1 (deferred to v0.6 / v0.7)

Recap of items explicitly not shipping in this patch, to keep a paper trail.

**v0.6 (next minor; design is `extensions_v4_design.md`):**
- `bridge_diagram(::Bicomodule)` + `BridgeDiagram` struct (Prop 3.20). Lands in `src/CatSharp.jl`.
- `is_conjunctive` + `ConjunctiveBicomodule(B)` (Cor 6.15). Symmetric to v0.5.1 #2.
- `weak_dual(p)` + `is_reflexive(p; depth=2)` (Example 7.2, single-var Dirichlet). Extends `src/Monoidal.jl`.
- Kleisli triple `(u, η, μ)` for `list_polynomial` + `comonoid_from_list_polynomial` + `[u/u] ≅ Fin^op` correspondence (Def 8.6).
- `span_from_linear_bicomodule` + `Span{A,B}` struct + finite-set pullback in `compose(::Span, ::Span)` + convenience constructor `linear_bicomodule_from_span(span)`.

**v0.7 (round that unblocks PolyAggregation v0.3 / Theorem 8.8 categorical realization):**
- Multi-variable Dirichlet ⊗ on `d-Set[c]` (paper §7.2-7.3, Lemma 7.13, Cor 7.15). The big one — what makes Theorem 8.8 land cleanly.
- Theorem 7.19 contravariant equivalence `Cat♯_lin ↔ Cat♯_disc,con` (gated on multi-var Dirichlet).
- Profunctor ↔ conjunctive bicomodule dictionary (§7.3.1, Prop 7.25).
- Generalize `kan_along_bicomodule` to general `(c, d)` (Prop 6.7).
- Duoidality natural map `(p◁q)⊗(p'◁q') → (p⊗p')◁(q⊗q')` (Prop 7.10, 7.17).

**Indefinitely deferred:**
- Continuous / measure-theoretic versions of `u`, `weak_dual`, etc. — different category.
- Full `*-autonomous` structure on the reflexive sub-category — wrappers + `weak_dual` are sufficient machinery for known consumers.
- Niu/Spivak Chapter 5 / Sprint 9 (still skipped per 2026-04-27 call).
- PolyViz Luxor → Makie/GraphMakie/TikzPictures rewrite (separate effort).
- Markov polynomials in any form (lives in PolyMarkov.jl).

---

## 9. References

- Spivak, Garner, Fairbanks. *Functorial Aggregation* (arXiv 2111.10968v7). The paper this whole arc — v0.5.1 + v0.6 + v0.7 — is implementing.
- `extensions_v4_design.md` — v0.6 design doc for the rest of the Cat♯ inspection + duality bundle. Q-resolution log in memory at `project_poly_v051_v06_resolved.md`.
- `polyaggregation_handoff.md` — bridge to PolyAggregation.jl satellite. §1 cross-references each PolyAggregation-side capability to the Poly.jl version that unblocks it.
- `polymarkov_handoff.md` — sibling bridge for PolyMarkov.jl; not gated by this patch.
- `ROADMAP.md` — cross-version phasing picture (v0.5.1 → v0.6 → v0.7 → satellites).
