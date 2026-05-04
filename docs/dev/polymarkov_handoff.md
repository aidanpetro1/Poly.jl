# Poly.jl → PolyMarkov.jl handoff

> **Status**: SKETCH, last updated 2026-05-04. Travels with the PolyMarkov.jl repo when it spins up — at that point this file is copied to PolyMarkov.jl's `docs/dev/extensions_v1_design.md` and the section on "what core needs to do first" becomes a "what core has done" status table. The architectural seed for PolyMarkov.jl was settled in `extensions_v3_design.md` §5 (2026-05-02); this doc is the bridge / boundary spec, not a re-derivation.
>
> **As of 2026-05-04:** PolyMarkov is still unblocked — v0.6 AbstractLens shipped. Subsequent v0.6 (PolyAggregation prereqs), v0.6.1 (Lemma 8.7 + coclosure), and v0.7-partial (full `BridgeDiagram`) Poly.jl releases all preserve the AbstractLens contract additively; PolyMarkov can pin against any tagged Poly.jl ≥ 0.6.

---

## 0. Why a separate library

PolyMarkov.jl implements stochastic / probabilistic polynomial-functor machinery — Kleisli-style "Markov lenses" with finitely-supported distributions on directions, Markov comonoids, probabilistic Moore machines, MDPs, HMMs. The 2026-05-02 decision (see `feedback_polymarkov_separate_library.md`) was to keep this out of Poly.jl core for three reasons:

- **Dependency hygiene.** Random number generation, tolerance configuration, and eventually `Distributions.jl` interop are all probabilistic-context dependencies that don't belong in a categorical-primitives library.
- **Equality semantics.** Markov category coherence laws hold "up to Kleisli equality" — equality of distributions, modulo a tolerance. Poly.jl's deterministic core uses on-the-nose `==`. Mixing the two semantics in one library creates confusing failure modes.
- **Independent cadence.** The Markov story will probably want to grow new distribution constructors, samplers, simulation backends, and `Distributions.jl` adapters faster than core categorical primitives evolve.

The dependency arrow is **strictly one-way**: `PolyMarkov.jl → Poly.jl`. Poly.jl never imports anything from PolyMarkov.

---

## 1. What Poly.jl needs to ship before PolyMarkov.jl can start

Unlike PolyAggregation.jl (which gates on multi-var Dirichlet in Poly.jl v0.7), **PolyMarkov.jl can spin up against Poly.jl v0.6 today.** The Markov twist sits entirely on the *lens layer* — polynomial objects, comonoid carriers, bicomodule carriers, and retrofunctor object-maps are all unchanged. Only the back-action of lenses goes stochastic.

| Capability | Paper / book reference | Poly.jl version | Status |
|---|---|---|---|
| `Lens` exposing `on_pos_fn` / `on_dir_fn` as accessor functions (not just struct fields) | — | v0.5 | already there; field access continues to work |
| `is_deterministic(::Lens) :: Bool` (trivially `true`) plus an `AbstractLens` supertype that `MarkovLens` can implement | — | v0.6 | **shipped 2026-05-03** |
| Documented extension contract for `<: AbstractLens` subtypes | — | v0.6 | **shipped — `docs/dev/abstract_lens.md`** |

**Architectural commitment shipped in v0.6 (read this carefully — it's narrower than QM4's "Path A" sketch below).** The `AbstractLens` supertype provides:

- The supertype itself, with `Lens <: AbstractLens`.
- Five generic functions a subtype must implement: `dom`, `cod`, `on_positions`, `on_directions`, `is_deterministic`.

It does **not** retype `compose`, `parallel`, `subst`, `*`, `+`, `▷`, `⊙`, `back_directions`, `polybox`, `lift`, etc. Those method bodies remain typed `::Lens`. PolyMarkov.jl's `MarkovLens` declares its own methods on its own type — there is no free arithmetic or composition inherited from the supertype. This is QM4-Path-A in spirit (single typed hierarchy, documented contract) but not in mechanism (signatures are not widened). Rationale: stochastic `compose` is a Kleisli bind, not function composition; widening signatures would create a polymorphic `compose` whose body works for one type and quietly errors for the other. The narrow form is honest about the boundary.

**Critical observation.** PolyMarkov.jl is *not gated* on any pending Poly.jl release. v0.6 is the floor; spin up against it whenever Aidan's priorities align.

---

## 2. What PolyMarkov.jl owns (the API surface)

The seed sketch from `extensions_v3_design.md` §5 stays as the design source-of-truth. Repeated here in compressed form for the boundary discussion; full prose lives in v3.

### 2.1 Phase A — Distribution and MarkovLens (foundation)

```julia
# PolyMarkov.jl/src/Distribution.jl
struct Distribution{T}
    support::Vector{T}
    probabilities::Vector{Float64}   # sums to 1 within tol
end
point, uniform, weighted              # constructors
sample, expectation, support, bind    # operations (bind = Kleisli bind)
≈                                     # equality up to tolerance

# PolyMarkov.jl/src/MarkovLens.jl
struct MarkovLens <: AbstractLens     # AbstractLens exported from Poly v0.6
    dom::Polynomial
    cod::AbstractPolynomial
    on_positions::Function            # i -> j  (deterministic)
    on_directions_stoch::Function     # (i, b) -> Distribution{Int}
end

identity_markov_lens(p::Polynomial) :: MarkovLens
compose(L::MarkovLens, M::MarkovLens) :: MarkovLens     # Kleisli
to_markov(L::Lens) :: MarkovLens                         # δ on each direction
is_deterministic(M::MarkovLens) :: Bool
to_lens(M::MarkovLens) :: Lens                           # errors if !is_deterministic
validate_markov_lens(M; atol=1e-9) :: Bool
```

### 2.2 Phase B — Markov polynomial structure operations

```julia
parallel(M::MarkovLens, N::MarkovLens) :: MarkovLens     # joint by independence
compose_subst(M::MarkovLens, N::MarkovLens) :: MarkovLens # Markov ▷
*(M::MarkovLens, N::MarkovLens) :: MarkovLens             # categorical product
+(M::MarkovLens, N::MarkovLens) :: MarkovLens             # categorical coproduct
```

### 2.3 Phase C — MarkovComonoid and MarkovDynamicalSystem

```julia
struct MarkovComonoid
    carrier::Polynomial
    eraser::MarkovLens                 # often deterministic
    duplicator::MarkovLens             # may be stochastic
end
validate_markov_comonoid(C; atol=1e-9) :: Bool

struct MarkovDynamicalSystem
    state_carrier::Polynomial          # S y^S
    interface::Polynomial
    update::MarkovLens
end
simulate(D::MarkovDynamicalSystem, s0, inputs::Vector; rng=Random.default_rng()) :: Vector
trace_distribution(D::MarkovDynamicalSystem, s0, inputs::Vector) :: Distribution
```

This is the headline modeling capability — HMMs, MDPs, Markov chains, all with categorical machinery underneath.

### 2.4 Phase D — Markov bicomodules and cofree (stretch)

```julia
struct MarkovBicomodule
    carrier::Polynomial
    left_base::MarkovComonoid
    right_base::MarkovComonoid
    left_coaction::MarkovLens
    right_coaction::MarkovLens
end

cofree_markov_comonoid(p::Polynomial, depth::Int) :: MarkovComonoid
# Carrier is a probability tree / decision tree
```

This phase is XL and depends on whether Phase C exposes a real demand for full structural parity. Keep it as v0.3+ work, after Phases A-C are in production use.

### 2.5 Worked examples PolyMarkov.jl ships

- `examples/markov_chain.jl` — a 3-state chain, transition matrix expressed as a `MarkovLens`.
- `examples/hmm.jl` — discrete HMM with observation model, decoding via Viterbi expressed as a Kleisli composition.
- `examples/mdp_gridworld.jl` — small gridworld MDP, value iteration as a fixpoint computation in the Markov category.
- `examples/markov_dyn_system_compose.jl` — composing two probabilistic Moore machines via `parallel` and `compose_subst`, demonstrating that Markov composition agrees with hand-derived joint distributions.

---

## 3. Boundary discipline

Same shape as PolyAggregation.jl. The rules:

**Allowed across the boundary (Poly.jl → PolyMarkov.jl, import side):**
- All Poly.jl public types — `Polynomial`, `Lens`, `Comonoid`, `Bicomodule`, `Retrofunctor`, `BicomoduleMorphism`, etc.
- All Poly.jl public operations — `compose`, `parallel`, `subst`, `kan_along_bicomodule`, `cofree_comonoid`, `free_labeled_transition_comonoid`, etc.
- The `validate_*` family.
- Symbolic-set machinery if PolyMarkov ever wants symbolic distributions (deferred to v0.4+).

**Not allowed across the boundary (anything PolyMarkov.jl introduces stays in PolyMarkov.jl):**
- `Distribution`, `MarkovLens`, `MarkovComonoid`, `MarkovBicomodule`, `MarkovDynamicalSystem` — these live in PolyMarkov.jl only.
- `point`, `uniform`, `weighted`, `sample`, `expectation`, `bind` — distribution operations stay in PolyMarkov.
- `simulate`, `trace_distribution`, `validate_markov_*` — same.
- Random number generation, tolerance constants (`MARKOV_TOL`, etc.), `Distributions.jl` adapters — same.

**Forbidden in both directions:**
- Cycles in either direction.
- Type piracy — PolyMarkov.jl never extends a Poly.jl method on a Poly.jl-owned type unless the method itself is owned by PolyMarkov.
- Monkey-patching.

If PolyMarkov.jl finds it needs a Poly.jl primitive that doesn't exist:
1. Open an issue on Poly.jl describing the use case.
2. Add the primitive to a future Poly.jl release.
3. PolyMarkov.jl bumps its `Poly` compat bound and uses the new primitive.

Never re-implement a Poly.jl primitive locally.

### 3.1 Lens extension contract — RESOLVED in v0.6

The QM4 question (Path A vs Path B) is **resolved**. v0.6 ships a hybrid: the supertype + accessor contract from Path A, with the responsibility distribution of Path B for arithmetic/composition. Concretely:

- **Inherited from Path A:** `MarkovLens <: AbstractLens`, single typed hierarchy, documented five-function interface (`dom`, `cod`, `on_positions`, `on_directions`, `is_deterministic`). Any code that wants to be polymorphic over both `Lens` and `MarkovLens` writes `::AbstractLens` and uses the accessors.
- **Inherited from Path B:** `compose`, `parallel`, `subst`, `*`, `+`, `▷`, `⊙`, `back_directions`, `polybox`, `lift`, etc. remain typed `::Lens`. PolyMarkov.jl defines its own `compose(::MarkovLens, ::MarkovLens)`, `parallel(::MarkovLens, ::MarkovLens)`, etc. Mixed-type calls are explicit conversions (`to_lens(M)` if deterministic, or `to_markov(L)` to lift) — no implicit polymorphism.

The full contract is in `docs/dev/abstract_lens.md`. The five accessors are exported from `Poly`, so `using Poly` brings them into scope. See `examples/abstract_lens_minimum_viable.jl` for a worked-example subtype that exercises the full interface end-to-end (including the explicit "no free arithmetic" demonstration: `compose(::IdentityLensWrapper, ::IdentityLensWrapper)` raises `MethodError`).

---

## 4. Repo layout and tooling

```
PolyMarkov.jl/
├── Project.toml          # depends on Poly ≥ 0.6
├── README.md
├── src/
│   ├── PolyMarkov.jl
│   ├── Distribution.jl
│   ├── MarkovLens.jl
│   ├── MarkovComonoid.jl
│   ├── MarkovDynamicalSystem.jl
│   ├── MarkovBicomodule.jl    # phase D, optional in v0.1
│   └── Validation.jl
├── test/
│   ├── runtests.jl
│   ├── test_distribution.jl
│   ├── test_markov_lens.jl
│   ├── test_markov_comonoid.jl
│   ├── test_markov_dyn_system.jl
│   └── test_simulate.jl
├── examples/
│   ├── markov_chain.jl
│   ├── hmm.jl
│   ├── mdp_gridworld.jl
│   └── markov_dyn_system_compose.jl
└── docs/
    ├── make.jl
    └── src/
        ├── index.md
        ├── concepts.md
        ├── api.md
        └── examples.md
```

Reuse Poly.jl's tooling: Documenter + Literate, same CI matrix (Julia 1.10, 1.11), same coverage / linting setup. Carry over the build-time gotchas (`remotes=nothing`, null-byte padding for Documenter on Windows) verbatim.

---

## 5. Initial release plan

**v0.1.0** — Phases A + B. `Distribution`, `MarkovLens`, basic operations (`compose`, `parallel`, `compose_subst`, `*`, `+`), `to_markov` / `to_lens` / `is_deterministic`, `validate_markov_lens`. Worked example: `markov_chain.jl`.

**v0.2.0** — Phase C. `MarkovComonoid`, `MarkovDynamicalSystem`, `simulate`, `trace_distribution`. Worked examples: `hmm.jl`, `mdp_gridworld.jl`, `markov_dyn_system_compose.jl`.

**v0.3.0** — Phase D (if demanded). `MarkovBicomodule`, `cofree_markov_comonoid`, Markov retrofunctors.

**v0.4.0+** — `Distributions.jl` interop in an extension package, possibly symbolic distributions (`Bernoulli(p::SymExpr)`).

Time estimate to v0.1.0: ~2 weeks. v0.2.0: another ~2 weeks. Calendar-wise, both could land before Poly.jl v0.7 is on `main`, since PolyMarkov is not gated on multi-var Dirichlet.

---

## 6. Open questions that travel with the spinout

These were flagged in `extensions_v3_design.md` §5 and `feedback_polymarkov_separate_library.md`. Marking them "for PolyMarkov.jl design round 1":

**QM1 (scope).** Phases A, A-B, A-C, or A-D in v0.1.0? *Recommendation:* A + B for v0.1.0, C for v0.2.0, D for v0.3.0. Each is a chunky enough release on its own.

**QM2 (`Distribution` representation).** Custom `Distribution{T}` struct (current sketch) or use `Dictionaries.jl` / a `Dict{T,Float64}`? *Recommendation:* custom struct for v0.1; revisit if `Dictionaries.jl` ergonomics start to matter.

**QM3 (tolerance config).** Module-level constant `MARKOV_TOL = 1e-9`, or per-call `atol` keyword? *Recommendation:* both — module-level default with per-call override.

**QM4 (Lens hierarchy).** ✅ **Resolved 2026-05-03.** Hybrid: Path A's supertype + five-function contract, Path B's per-subtype responsibility for `compose` / `parallel` / `subst` / etc. See §3.1 for the resolved contract. Poly.jl v0.6 is the floor.

**QM5 (equality).** `==` strict (errors on tolerance-required comparisons) or always-tolerated `≈`? *Recommendation:* `==` strict on `Distribution`s (compares supports + probabilities exactly); `≈` is the tolerance-aware version. Coherence checks default to `≈`. Same convention as `Float64`.

**QM6 (simulate API).** `simulate` returns a `Vector{State}` (single seeded run) or `Distribution{Vector{State}}` (full trace distribution)? *Recommendation:* both — `simulate(D, s0, inputs; rng=...)` returns a single sample, `trace_distribution(D, s0, inputs)` returns the distribution. Naming discipline keeps confusion away.

**QM7 (naming).** `MarkovLens` vs `StochLens`, `MarkovComonoid` vs `StochComonoid`. The Markov-category literature is split; Spivak uses "Markov." *Recommendation:* `Markov*` throughout, matching Spivak and Fritz et al. Document the alias if anyone reads "Stoch" in the literature.

**QM8 (package boundaries).** Is `Distribution{T}` itself worth factoring out into a tiny `FinDistributions.jl` shared with PolyAggregation.jl? *Recommendation:* not yet. If PolyAggregation actually needs the same type, factor it then. Premature decomposition is a Bad Time.

---

## 7. Differences from PolyAggregation.jl handoff (architectural notes)

The two satellite libraries are *structurally different* in how they extend Poly.jl, and it's worth being explicit so future Poly.jl design doesn't accidentally treat them as interchangeable:

| | PolyMarkov.jl | PolyAggregation.jl |
|---|---|---|
| Where it twists Poly | The *morphism* layer (lenses become Kleisli) | The *application* layer (new types over existing primitives) |
| Polynomial objects | Unchanged | Unchanged |
| Comonoids / categories | Wrapped in a stochastic version (`MarkovComonoid`) | Used as-is to represent schemas |
| Lenses | Replaced with `MarkovLens` | Used as-is |
| Bicomodules | Wrapped (`MarkovBicomodule`, phase D) | Used as-is + new application types on top |
| Gating Poly.jl version | v0.6 (for `AbstractLens`) or v0.5 (Path B) | **v0.7 (for multi-var Dirichlet ⊗)** |
| Spinout urgency | Ready when Aidan wants | Wait for v0.7 |
| Domain dependencies | RNG, tolerance, eventually `Distributions.jl` | Storage backends, eventually `DataFrames.jl`, `SQLite.jl` |
| Categorical depth needed | Markov categories (Fritz et al.) | Multi-var polynomial functor + module theory |

The takeaway: **PolyMarkov is a Kleisli twist; PolyAggregation is a universal-construction application.** This is also why PolyMarkov can spin up nearly today and PolyAggregation has to wait — you can layer Kleisli on top of any deterministic categorical setup, but applying universal constructions requires the constructions to actually exist in core first.

If a third satellite library ever materializes (`PolyMDP.jl`? `PolyDB.jl`? `PolyOptics.jl`?), it'll fall into one of these two patterns or — rarely — a third "new monoidal structure" pattern that would need its own bridge doc template. The two patterns documented here cover the easy cases.

---

## 8. Cross-reference

- `extensions_v3_design.md` §5 — the original Markov design seed (2026-05-02). Stays as-is until PolyMarkov.jl spins up; at that point its content is migrated 