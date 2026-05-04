# PolyMarkov.jl: green light — Poly.jl v0.6 is ready

> **For:** PolyMarkov.jl spinup team.
> **Date:** 2026-05-03.
> **Read first.** This is the short, action-oriented "go" notice. The full design discussion is in `polymarkov_handoff.md` — read that for design context, the API surface sketch, and the boundary discipline. This file is the handoff letter.

---

## What just shipped in Poly.jl v0.6

`AbstractLens` and the five-function lens interface. Concretely:

- `abstract type AbstractLens` declared in `src/Lens.jl`. `Lens <: AbstractLens`.
- Five accessor / predicate functions exported from `Poly`:
  - `dom(L::AbstractLens) -> AbstractPolynomial`
  - `cod(L::AbstractLens) -> AbstractPolynomial`
  - `on_positions(L::AbstractLens)`
  - `on_directions(L::AbstractLens)`
  - `is_deterministic(L::AbstractLens)::Bool`
- Default implementations on `Lens` are pure field returns. Existing field access (`f.on_positions` etc.) continues to work — purely additive change, zero breaking.
- `docs/dev/abstract_lens.md` — the extension contract.
- `examples/abstract_lens_minimum_viable.jl` — worked-example subtype (`IdentityLensWrapper <: AbstractLens`) exercising the interface end-to-end and demonstrating that subtypes don't get free arithmetic.
- `test/test_v06_abstract_lens.jl` — green (20/20). Full `runtests.jl` green (1298/1298).

`Project.toml` now declares `version = "0.6.0"`. Set `Poly = "0.6"` in PolyMarkov's `Project.toml` `[compat]`.

---

## Architectural commitment — read this before writing any `MarkovLens` code

QM4 is **resolved as a hybrid, not pure Path A.** The supertype gives you signature compatibility and a documented contract. It does **not** give you free implementations of `compose`, `parallel`, `subst`, `*`, `+`, `▷`, `⊙`, `back_directions`, `polybox`, `lift`, etc. — those method bodies remain typed `::Lens` in Poly.jl.

What this means for PolyMarkov.jl:

1. **Yes:** declare `struct MarkovLens <: AbstractLens` and implement the five accessors.
2. **Yes:** any code wanting polymorphism over deterministic and stochastic lenses uses `::AbstractLens` and routes through the accessors.
3. **No:** `compose(M::MarkovLens, N::MarkovLens)` is not inherited. PolyMarkov.jl defines that method itself. Same for `parallel`, `subst`, `*`, `+`, `▷`, etc.
4. **No:** mixed-type calls (`compose(::Lens, ::MarkovLens)`) are not handled by the supertype. PolyMarkov.jl provides explicit conversions: `to_lens(M::MarkovLens)::Lens` (errors if `!is_deterministic(M)`) and `to_markov(L::Lens)::MarkovLens` (lifts via point masses).

Rationale: a stochastic `compose` is a Kleisli bind on the back-action, not function composition. Widening Poly.jl's `compose` to `::AbstractLens` would give a polymorphic generic whose body works for `Lens` and silently errors on `MarkovLens`. The narrow form is honest about the boundary.

The full extension contract is in `docs/dev/abstract_lens.md` — read that file before writing `MarkovLens.jl`.

---

## Day-1 task list for PolyMarkov.jl

In rough order — see §4 of `polymarkov_handoff.md` for the full repo layout.

1. `Project.toml` with `Poly = "0.6"` in `[compat]`.
2. `src/Distribution.jl` — finitely-supported `Distribution{T}`, `point` / `uniform` / `weighted`, `bind`, `≈` with tolerance.
3. `src/MarkovLens.jl` — `struct MarkovLens <: AbstractLens` with fields per §2.1 of the handoff. Implement all five `AbstractLens` methods. Implement `compose(::MarkovLens, ::MarkovLens)` via Kleisli bind on the back-action. Implement `to_lens(::MarkovLens)::Lens` and `to_markov(::Lens)::MarkovLens` for explicit boundary crossing.
4. `test/test_markov_lens.jl` — at minimum: identity is deterministic, `to_markov(identity_lens(p)) ≈ identity_markov_lens(p)`, `to_lens(to_markov(L)) ≈ L`, Kleisli associativity up to `≈`, the round-trip `is_deterministic(M) && to_lens(M) ≈ L` for `M = to_markov(L)`.
5. `examples/markov_chain.jl` — the headline worked example. A 3-state chain, transitions encoded as a `MarkovLens`, one step verified by hand.

That's a v0.1.0-Phase-A release. Phase B (`parallel`, `compose_subst`, `*`, `+`) and Phase C (`MarkovComonoid`, `MarkovDynamicalSystem`, `simulate`, `trace_distribution`) follow per the handoff's release plan.

---

## Reference index

Inside Poly.jl v0.6:

- `src/Lens.jl` — `AbstractLens` at line ~23, `Lens <: AbstractLens` at line ~54, accessors at lines ~99–138.
- `src/Poly.jl` — exports at lines ~64–67.
- `docs/dev/abstract_lens.md` — extension contract.
- `examples/abstract_lens_minimum_viable.jl` — minimum-viable subtype demo. Read it before writing `MarkovLens`.
- `CHANGELOG.md` — top entry, `## [Unreleased] — v0.6 AbstractLens (2026-05-03)`.
- `test/test_v06_abstract_lens.jl` — five-testset reference for what a subtype's smoke tests should look like.

Inside this docs directory:

- `polymarkov_handoff.md` — the long-form bridge / boundary doc. The QM4 row in §6 and §3.1 are now resolved per the v0.6 commitment above.
- `feedback_polymarkov_separate_library.md` — the separate-library decision rule.
- `extensions_v3_design.md` §5 — the original Markov design seed (2026-05-02). Migrate to PolyMarkov's own design doc on spinup.

---

## What core will and won't do for you

**Will:**

- Stay backward compatible on the `AbstractLens` interface across v0.6.x.
- Add new accessors only with an explicit major-version bump and an upgrade note for subtype implementers.
- Expose any new public types/operations that PolyMarkov asks for via issue (the rule: open an issue, don't reimplement locally).

**Won't:**

- Add probabilistic / stochastic concepts to core. Distributions, RNG, tolerance constants, `Distributions.jl` adapters all live in PolyMarkov.jl per the separate-library decision.
- Widen `::Lens`-typed methods to `::AbstractLens` without a deliberate v0.7+ design pass. If PolyMarkov hits a case where this would meaningfully simplify the API, file an issue.
- Test PolyMarkov-side behavior in core's CI. Each side's testset stays in its own repo.

---

## Open contact points

If anything in `docs/dev/abstract_lens.md` or this notice is ambiguous, file the question against Poly.jl rather than working around it locally — the contract is meant to be tight enough that subtype authors don't have to guess. First spinup is the highest-leverage moment to flag interface gaps.

Good hunting.
