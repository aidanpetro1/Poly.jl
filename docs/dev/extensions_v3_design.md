# Poly.jl — Extensions v3 Design Doc (v0.4 release)

> **Status**: SKETCH, 2026-05-02. Not yet signed off. Open questions in §6 — please resolve in a structured Q&A round before implementation begins, as with v1 / v2.

---

## 0. Summary

| # | Item | Class | Breaks API? | PR size | Depends on |
|---|---|---|---|---|---|
| 1 | Symbolic non-identity `D` for `kan_2cat` (right and left) | Carryover from v0.3.1 | No (additive) | L | — |
| 2 | Truly-lazy `LazyBicomoduleCarrier` (no validator-driven materialize) | Carryover from v0.3.1 | No (additive) | M | — |
| 3 | Remove `free_category_comonoid` deprecation shim | Carryover from v0.3.1 | **Hard** (drops shim) | XS | — |
| 4 | `cofree_comonoid(::Comonoid, depth)` — universal property + `factor_through` | Deferred from v2 (#13) | No (additive) | L | — |

**Phasing.** v0.4 = carryovers (#1–#4). Markov polynomials moved to a separate library, **PolyMarkov.jl** — see §5 for the brief and the link forward.

**Where the codebase stands today.** v0.3.1 shipped the full Niu/Spivak coequalizer for `compose(::Bicomodule, ::Bicomodule)`, identity-D right-Kan, `free_labeled_transition_comonoid` (with `Base.depwarn` shim on the old name), and a polish bundle (n-ary `parallel`, `behavior_tree_from_paths`, opt-out validation, Project.toml→0.3.1). All 11 test files green locally on Julia 1.10.5. Three deferrals were committed to v0.4: items #1, #2, #3 below.

---

## 1. Symbolic non-identity `D` for `kan_2cat`

**Problem.** `kan_2cat(D, F; direction)` currently handles identity `D` only; non-identity `D` errors with a v0.3.x pointer. The blocker is that the symbolic-layer coequalizer needed for the construction does not yet exist — finite `kan_along_bicomodule` builds via Niu/Spivak Ch. 8 colimit-as-coequalizer (Prop 8.88), but the symbolic version requires reasoning about `SymbolicSet` quotients, which we have stub-level support for at best.

### 1.1 Proposed design

Build a `SymbolicCoequalizer{T}` primitive in `src/Symbolic.jl`:

```julia
struct SymbolicCoequalizer{T} <: SymbolicSet
    parent::SymbolicSet                  # the source set being quotiented
    relation::Vector{Tuple{SymExpr,SymExpr}}  # generating equations
    cardinality::Cardinality             # may be Symbolic / Unknown
end
```

`kan_2cat` then walks the existing finite construction but emits `SymbolicCoequalizer` whenever a position-set or direction-set would otherwise need finite enumeration. The unit / counit lenses become `SymbolicLens`. `factor_through` works symbolically: pattern-match the input morphism against the coequalizer's relation and return the unique factorizing lens.

**Right-direction.** Same construction dualized — `Π_D` builds via the symbolic right-Kan section formula. The identity-D fast path stays unchanged.

### 1.2 Tests

- Identity-D round-trip: `kan_2cat(I_C, F)` returns `F` (already covered, regression-only).
- One-position non-identity D (still finite): finite and symbolic constructions produce the same `KanExtension` up to behavioral equivalence on a few concrete inputs.
- Truly-symbolic D (e.g., `D` with `SymbolicSet` carrier of unknown cardinality): construction succeeds, `factor_through` works on a symbolically-stated 2-cell.

### 1.3 Out of scope

- Continuous / measure-theoretic `D`. Stays out — finite + symbolic-finitary only.
- Optimization of the symbolic relation set (no normalization pass; if a user wants minimal generating equations they call a separate `simplify_coequalizer` helper, design TBD).

---

## 2. Truly-lazy `LazyBicomoduleCarrier`

**Problem.** v0.3.1 introduced `LazyBicomoduleCarrier <: AbstractPolynomial` (Cofree.jl:1058), but the validator (`validate_bicomodule_detailed`) currently materializes it via `compose(M, N)` because the validator's `===` checks on `Polynomial` need a concrete carrier. So "lazy" today means "the user-facing accessor is lazy, but everything past the front door pulls the trigger anyway."

### 2.1 Proposed design

Two changes:

1. Generalize `validate_bicomodule_detailed` to accept `AbstractPolynomial`. When given a lazy carrier, it walks position-by-position via `position_at(::LazyBicomoduleCarrier, i)` and `direction_at`, never materializing the whole carrier. Counit/coassoc/compatibility checks become per-position.

2. Lift the `===` invariants on `compose`, `whisker_*`, and `horizontal_compose` to allow lazy operands: instead of `M.right_base.carrier === N.left_base.carrier`, use behavioral equivalence (`is_subst_of`-style) with a fast path through `===` when both are concrete.

The end goal: `compose_lazy(M, N) |> validate_bicomodule_detailed` runs in time linear in the number of positions actually inspected, rather than `|positions(compose(M,N))|`.

### 2.2 Tests

- Adversarial: build an `M ⊙_lazy N` whose materialized carrier would have ~10⁴ positions. Validator runs on a sampled subset (or the full set) without materializing.
- Property: lazy and concrete validators agree on the truth value for every Bicomodule that fits in memory both ways.

### 2.3 Out of scope

- Lazy `compose` of *three* bicomodules that returns a `LazyLazyBicomoduleCarrier`. The current `compose_lazy(compose_lazy(M,N), P)` materializes the inner one. Acceptable for now.

---

## 3. Remove `free_category_comonoid` deprecation shim

**Problem.** v0.3.1 deprecated `free_category_comonoid` in favor of `free_labeled_transition_comonoid`, with a `Base.depwarn` shim that translates edge-tuple shape and keyword names. The shim was scoped for one minor; v0.4 drops it.

### 3.1 Proposed design

Delete the shim from `src/Comonoid.jl`. CHANGELOG entry under "Removed". Document the migration path in the v0.4 release notes (one paragraph: "if you were calling `free_category_comonoid(vertices, edges)` with `(src, tgt)` or `(src, tgt, label)` edges, switch to `free_labeled_transition_comonoid(positions, edges)` with `(src, label, tgt)` edges").

### 3.2 Tests

- Existing callers in `test/` already migrated in v0.3.1; v0.4 just removes the shim's targeted tests.

---

## 4. `cofree_comonoid(::Comonoid, depth)` — universal property + `factor_through`

**Problem.** Item #13 was deferred from v2 because the universal property of cofree-on-a-comonoid is fuzzy enough that doing it half-right would be worse than skipping. The companion note `docs/dev/cofree_over_comonoid.md` was supposed to land before any v3 work.

### 4.1 Proposed design

Companion note first (`docs/dev/cofree_over_comonoid.md`) covering:

- Statement of the universal property (Niu/Spivak Ch. 8 — the cofree comonoid on a polynomial is the right adjoint to the forgetful `Cat# → Poly`; cofree-on-a-comonoid is more delicate, sitting at the level of comodules).
- Choice of construction: tree-of-comonoid-paths vs. limit-of-finite-truncations. Fix one.
- Statement of what `factor_through(c, F)` exhibits and what it doesn't.

Then implementation:

```julia
struct CofreeOverComonoid
    base::Comonoid
    depth::Int
    cofree::Comonoid               # the carrier comonoid
    counit::BicomoduleMorphism     # exhibiting the universal property
end

cofree_comonoid(c::Comonoid, depth::Int) :: CofreeOverComonoid
factor_through(coc::CofreeOverComonoid, α::BicomoduleMorphism) :: BicomoduleMorphism
```

The `depth` parameter is the same truncation knob as `cofree_universal`; the universal property holds element-wise (matching `validate_retrofunctor(...; strict=false)`'s convention), with documented limitations in the docstring.

### 4.2 Tests

- Counit composes correctly on identity inputs.
- `factor_through` round-trip: given α: M → cofree(c, d), check `compose(factor_through(coc, α), counit) ≈ α` element-wise on all positions.
- Comparison: `cofree_comonoid(eraser_only_comonoid, d)` agrees with `cofree(carrier, d)` from v2.

### 4.3 Out of scope

- Lazy cofree-on-comonoid (mirror of #8 from v2). Defer to v3.5/v0.5 unless modeling work demands it.

---

## 5. Markov polynomials — separate library (PolyMarkov.jl)

> **Decision (2026-05-02):** Markov polynomials live in a separate package, not Poly.jl core. Keeps Poly.jl free of probabilistic dependencies (RNG, tolerance config, eventually `Distributions.jl`) and lets the Markov story evolve on its own release cadence.

The design sketch below is preserved in this doc as the seed for the PolyMarkov.jl repo. When we spin up that package, it gets its own `extensions_v1_design.md` and we move the relevant parts there.

### 5.1 What we mean by "Markov polynomial"

A polynomial functor's *shape* is unchanged: positions are a set, and at each position there is a direction-set. What changes is the **category in which lenses live**. A *Markov lens* `(f₁, f♯) : p ⇄ q` has:

- `f₁ : positions(p) → positions(q)` — deterministic on positions (same as before).
- `f♯ : (i, b) → Distribution(p[i])` — for each `i ∈ positions(p)` and `b ∈ q[f₁(i)]`, a finitely-supported probability distribution over directions of `p` at `i`.

Composition is **Kleisli composition** for the distribution monad: marginal-out the intermediate direction. Identity Markov lens has `f♯(i, b) = δ_b` (point distribution).

> *Why it's still a polynomial functor.* The polynomial `p = Σ y^{p[i]}` denotes a Set-valued functor. The Markov twist is on the *morphism* category — `Poly` becomes the Kleisli category of `D ∘ (-)` rather than just `Set`-valued natural transformations. Positions / directions stay sets; only the "back-action" goes stochastic. Continuous distributions are out of scope for v0.4.

This matches Spivak's "Polynomial functors and stochastic processes" framing and the broader Markov-category program (Fritz et al., 2020).

### 5.2 Phase A — `Distribution` and `MarkovLens` (the foundation)

```julia
# src/Markov.jl

struct Distribution{T}
    support::Vector{T}
    probabilities::Vector{Float64}   # same length as support; sums to 1 (within tol)
end

# Constructors
point(x::T) where T = Distribution{T}([x], [1.0])
uniform(xs::Vector{T}) where T = Distribution{T}(xs, fill(1/length(xs), length(xs)))
weighted(xs::Vector{T}, ws::Vector{Float64}) where T  # normalizes; validates ≥ 0

# Operations
sample(d::Distribution{T}, rng=Random.default_rng()) :: T
expectation(f, d::Distribution{T}) :: Real            # f : T → ℝ
support(d::Distribution{T}) :: Vector{T}              # Fairbanks-style support, distinct values
bind(f, d::Distribution{T}) :: Distribution{S}        # Kleisli bind, f : T → Distribution{S}

# Equality up to tolerance (always tolerated; see Q5.4)
≈(d1::Distribution, d2::Distribution; atol=1e-9) :: Bool


struct MarkovLens
    dom::Polynomial
    cod::AbstractPolynomial
    on_positions::Function           # i -> j  (deterministic)
    on_directions_stoch::Function    # (i, b) -> Distribution{Int}  (or whatever direction type)
end

# Categorical structure
identity_markov_lens(p::Polynomial) :: MarkovLens
compose(L::MarkovLens, M::MarkovLens) :: MarkovLens   # Kleisli

# Conversion
to_markov(L::Lens) :: MarkovLens                       # f♯(i,b) = point(L.on_directions(i,b))
is_deterministic(M::MarkovLens) :: Bool               # all f♯(i,b) are point distributions
to_lens(M::MarkovLens) :: Lens                         # errors if !is_deterministic
```

**Validator.** `validate_markov_lens(M; atol=1e-9)`:

- For each `i ∈ positions(dom)` and `b ∈ cod[f₁(i)]`, the distribution `f♯(i,b)` is supported on `directions(dom[i])` and probabilities sum to 1.

### 5.3 Phase B — Markov polynomial structure (`⊗`, `▷`, named ops)

The polynomial *objects* are unchanged; we only need new lens-level operations.

- `parallel(M::MarkovLens, N::MarkovLens) :: MarkovLens` — independent product on directions, joint distribution by independence (`bind` over both).
- `compose_subst(M::MarkovLens, N::MarkovLens) :: MarkovLens` — substitution composition `▷` on Markov lenses; the inner direction sample feeds into the outer lens.
- `*` and `+` on Markov lenses (categorical product / coproduct).

### 5.4 Phase C — `MarkovComonoid` and `MarkovDynamicalSystem`

```julia
struct MarkovComonoid
    carrier::Polynomial
    eraser::MarkovLens         # carrier → y;  often deterministic
    duplicator::MarkovLens     # carrier → carrier ▷ carrier;  may be stochastic
end

# A probabilistic Moore machine / MDP-like dynamical system.
struct MarkovDynamicalSystem
    state_carrier::Polynomial     # S y^S
    interface::Polynomial         # the polynomial p with output positions / input directions
    update::MarkovLens            # state_carrier ⇄ interface, stochastic on directions
end

simulate(D::MarkovDynamicalSystem, s0, inputs::Vector; rng=...) :: Vector{State}
```

Comonoid coherence: the standard counit + coassoc laws hold *up to Kleisli equality* (= equality of distributions, within tol). `validate_markov_comonoid` is the natural generalization of `validate_comonoid`.

This phase delivers the headline modeling capability — you can write down an HMM, a small MDP, or a Markov chain and simulate it, with all the categorical machinery sitting underneath.

### 5.5 Phase D — Markov bicomodules and cofree (stretch / scope question)

If we want full structural parity:

- `MarkovBicomodule` — bicomodule between two `MarkovComonoid`s, coactions are Markov lenses.
- `cofree_markov_comonoid(p, depth)` — the cofree Markov comonoid on a polynomial. Underlying carrier looks like a *probability tree* / decision tree where each branching is a distribution.
- Markov retrofunctors (= functors of Markov categories).

This is XL on its own and might better land in v0.5. Q5.0 below.

### 5.6 What stays out

- Continuous distributions / measure theory. Hard for a reason; needs a `MeasurableSet` story we don't have.
- `Distributions.jl` interop. Doable later as a thin adapter; for v0.4 we use our own finitely-supported `Distribution{T}` for correctness and reproducibility.
- Symbolic distributions (e.g. `Bernoulli(p)` with `p::SymExpr`). Possible v3.5 follow-up if symbolic modeling needs it.
- Bayesian inference / belief updates. Different category (Markov categories with daggers); separate package.

---

## 6. Open questions

### Carryover items (#1–#4)

**Q1.1** — `kan_2cat` symbolic-coequalizer: ship right-direction in v0.4, or split (left-symbolic in v0.4, right-symbolic in v0.4.1)? *Recommendation:* both directions in v0.4. The dualization is mechanical once left works; splitting just adds release overhead.

**Q1.2** — `SymbolicCoequalizer.relation`: store as `Vector{Tuple{SymExpr,SymExpr}}` (above) or as a quotient-by-congruence-relation type? *Recommendation:* the simple Vector for v0.4; revisit if `simplify_coequalizer` needs richer structure.

**Q2.1** — Truly-lazy validator: keep `validate_bicomodule_detailed` as one method that branches on `<: AbstractPolynomial`, or introduce `validate_lazy_bicomodule_detailed` as a separate entry point? *Recommendation:* one method, internal dispatch; mirrors how `support` works on `PolyElement`.

**Q3.1** — Migration grace period: drop the shim cleanly (v0.4 breaking), or keep it deprecated for one more minor and remove in v0.5? *Recommendation:* drop in v0.4. v0.3.1 has been out long enough; downstream PolyCDS code is the only known caller and you control it.

**Q4.1** — `cofree_comonoid` companion note: write it before or alongside the implementation PR? *Recommendation:* before, like `kan_extensions_construction.md`.

**Q4.2** — `factor_through` semantics: element-wise (matching `strict=false` retrofunctor convention) or strict? *Recommendation:* element-wise, with a `strict::Bool` keyword that defaults to `false`. Document the divergence.

### Markov track

Lives in PolyMarkov.jl, not v0.4. Open questions for that repo (Q5.0 scope, Distribution struct vs. Dictionaries, tolerance config, Lens hierarchy, equality, simulation API, naming, package boundaries) carry over to the PolyMarkov.jl design doc when we spin it up. See §5 above for the seed sketch.

---

## 7. Phasing / release plan

v0.4 ships the four carryovers (#1–#4). PR ordering — likely #3 (drop shim, mechanical) → #2 (truly-lazy carrier) → #1 (symbolic kan_2cat) → #4 (cofree-on-comonoid, gated on companion note). PolyMarkov.jl spins up as its own repo on whatever cadence fits.

---

## 8. Out of scope

- Niu/Spivak Chapter 5 / Sprint 9 (adjoint quadruple Set/Poly, factorizations, cartesian closure, base change). Still skipped per your 2026-04-27 call — structural rather than modeling-helping.
- PolyViz Luxor → Makie/GraphMakie/TikzPictures rewrite. Still on the standing todo, separate effort.
- Catlab.jl integration revisit. Same.
- Performance pass on Sprint 8's tree enumeration. Same.
- Markov polynomials in any form — moved to PolyMarkov.jl as a separate library.
