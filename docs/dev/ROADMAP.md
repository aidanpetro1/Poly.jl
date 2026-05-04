# Poly.jl — Roadmap

Cross-version picture of where Poly.jl is, where it's going, and how the satellite libraries (PolyMarkov.jl, PolyAggregation.jl) fit. Last updated 2026-05-04 (v0.6 + v0.6.1 implemented + tested).

This doc is the map. Each version row links to the design doc (if any) and progress notes that capture the detail. When picking up work in a new session, start here, then jump to the linked design doc.

---

## At-a-glance

| Version | Theme | Status | Design doc | Progress note |
|---|---|---|---|---|
| v0.1.0 | Initial release: polynomials, lenses, monoidal | shipped | `historical-design.md` | git tag `v0.1.0` |
| v0.2.0 | Extensions v1 (8 PRs from external review) | shipped | `extensions_v1_design.md` | git tag `v0.2.0` |
| v0.3.0 | Extensions v2 (28 Qs, 7 rounds; Cat♯ scaffolding) | shipped | `extensions_v2_design.md` | git tag `v0.3.0` |
| v0.3.1 | Concrete Poly v0.3.x asks (10 priorities) | shipped | — | git tag `v0.3.1` |
| v0.4 + v0.4.x | Cat♯-completeness: base_change, cofree_morphism, tuple_retrofunctor, forward-action patch | shipped, awaiting tag | `extensions_v3_design.md` | memory: `project_poly_v04_progress.md` |
| v0.5 | `validate_retrofunctor_forward` for partial-image retrofunctors | shipped, awaiting tag | `forward_action.md` | memory: `project_poly_v05_validate_forward.md` |
| v0.6 AbstractLens | `AbstractLens` supertype, accessor protocol | shipped, awaiting tag | `abstract_lens.md` | CHANGELOG `[Unreleased]` |
| v0.5.1 | PolyAggregation minimum-surface patch (5 items) | shipped, awaiting tag | `extensions_v5_design.md` | memory: `project_poly_v051_implemented.md` |
| v0.6 | PolyAggregation v0.3.0 prereqs (4 items: bridge_diagram, weak_dual, span_from_linear_bicomodule, comonoid_from_list_polynomial) | shipped, awaiting tag | `extensions_v4_design.md` | `handoff_2026-05-04_v06_v061.md` |
| v0.6.1 | Paper-faithful Lemma 8.7 + coclosure (coclosure, comonoid_from_coclosure, is_reflexive; replaces v0.6's #3 stub) | shipped, awaiting tag | (paper-driven, no separate design doc) | `handoff_2026-05-04_v06_v061.md` |
| v0.7-partial | Full Prop 3.20 bridge: `BridgeDiagram` struct with `(B, E, π, S, T)` data, backward-compatible with v0.6 | shipped, awaiting tag | `extensions_v6_design.md` (§7) | `handoff_2026-05-04_v06_v061.md` |
| **v0.7-main** | **Multi-variable Dirichlet ⊗ + Theorem 7.19 + profunctor↔conjunctive + generalized Kan + duoidality + symbolic coclosure (~5 weeks)** | **planned, design doc landed** | **`extensions_v6_design.md`** | — |

> **Tagging note.** Several recent versions (v0.4, v0.4.x, v0.5, v0.6 AbstractLens) shipped to `main` but haven't been tagged on GitHub yet. The git tag inventory currently goes through `v0.3.1`. The numbering choices here follow the CHANGELOG and Project.toml; the v0.5.1 / v0.6 / v0.7 labels for upcoming work assume the existing unreleased entries land first. If the next tag-and-release pass renumbers anything, the design docs can keep their current titles and just update this table.

---

## Upcoming work in detail

### v0.5.1 — PolyAggregation minimum-surface patch ✓ shipped

**Status:** all 5 items implemented in `main` and tests pass. Awaiting a git tag (see "Tag housekeeping" below).

**Goal (achieved):** unblock PolyAggregation.jl v0.2.0 (data-level `aggregate(::Instance)` working end-to-end on the four worked examples).

**Scope (shipped):**

| Item | File | Notes |
|---|---|---|
| `list_polynomial(; max_size=nothing)` | `src/Demos.jl` | Function form; `NatSet()` positions by default, `FinPolySet(0:K)` when truncated |
| `is_linear(B)` + `LinearBicomodule(B)` | new `src/CatSharp.jl` | Validate-and-wrap, never mutate. `is_linear(::Bicomodule)` coexists with the polynomial predicate via dispatch |
| `linear_bicomodule_from_span(C, D, S, s, t; validate=true)` | `src/CatSharp.jl` | Forward direction with trivial action; validates for discrete bases |
| `c_one_y(c::Comonoid)` | `src/CatSharp.jl` | Theorem 8.8 carrier as a **c-1 bicomodule** (right base = unit comonoid) with cod-tracking left action — see `polyaggregation_handoff.md` §1.1 for the deviation rationale |
| `morphisms_out_of(c, a)` + `cod_in_comonoid(c, a, f)` | `src/Comonoid.jl` | Discoverable wrappers around `direction_at` / `c.duplicator.on_positions` |

**Tests:** `test/test_v051_polyaggregation_surface.jl` — 5 testsets, wired into `runtests.jl`. All green.

**Design doc:** [`extensions_v5_design.md`](./extensions_v5_design.md). The v0.5.1 implementation deviates from §4 of the design doc on `c_one_y`'s base typing and left-action choice — see implementation memory note `project_poly_v051_implemented.md` for the trace.

**Resolved Qs:** all 15 from `extensions_v4_design.md` §7 plus one phasing decision; see memory `project_poly_v051_v06_resolved.md`.

### v0.6 — Cat♯ inspection + duality bundle

**Goal:** complete the Cat♯-flavored introspection layer that v0.5.1 leaves half-built. Lands `bridge_diagram` (Prop 3.20), the conjunctive half of the linear/conjunctive split, weak duality on single-variable Dirichlet, the Kleisli triple completing the list polynomial story, and the reverse direction of the span↔linear-bicomodule dictionary.

**Scope:**

| Item | File | Notes |
|---|---|---|
| `bridge_diagram(::Bicomodule)` + `BridgeDiagram` struct (Prop 3.20) | `src/CatSharp.jl` (extends) | Carries source Bicomodule reference; étale-leg validator runs in constructor by default |
| `is_conjunctive` + `ConjunctiveBicomodule(B)` (Cor 6.15) | `src/CatSharp.jl` (extends) | Symmetric with v0.5.1 linear half |
| `weak_dual(p)` + `is_reflexive(p; depth=2)` (Example 7.2) | `src/Monoidal.jl` (extends) | Single-var Dirichlet only; multi-var → v0.7 |
| Kleisli triple `(u, η, μ)` + `comonoid_from_list_polynomial` (Def 8.6) | `src/Demos.jl` (extends) | μ is needed by the v0.6 reverse-span work; natural home |
| `span_from_linear_bicomodule` + `Span{A,B}` struct + finite-set pullback in `compose(::Span, ::Span)` (Cor 6.17, reverse direction) | `src/CatSharp.jl` (extends) | Own thin Span struct, no Catlab dep; convenience constructor `linear_bicomodule_from_span(span)` lands here too |

**Estimated effort:** ~3 weeks focused work. PR ordering: bridge_diagram → ConjunctiveBicomodule → weak_dual → Kleisli triple → span_from_linear_bicomodule.

**Design doc:** [`extensions_v4_design.md`](./extensions_v4_design.md). Q-resolution complete; the doc's §7 questions are answered in memory `project_poly_v051_v06_resolved.md`.

### v0.7 — Multi-variable Dirichlet ⊗ + Theorem 7.19 + profunctor↔conjunctive

**Goal:** the round that unblocks PolyAggregation v0.3 (full Theorem 8.8 categorical realization) and gives Cat♯ Kan extensions general bases.

**Scope:**
- Multi-variable Dirichlet ⊗ on `d-Set[c]` (paper §7.2-7.3, Lemma 7.13, Cor 7.15).
- Theorem 7.19 contravariant equivalence `Cat♯_lin ↔ Cat♯_disc,con` (gated on multi-var Dirichlet).
- Profunctor ↔ conjunctive bicomodule dictionary (§7.3.1, Prop 7.25).
- Generalize `kan_along_bicomodule` to general `(c, d)` (Prop 6.7).
- Duoidality natural map `(p◁q)⊗(p'◁q') → (p⊗p')◁(q⊗q')` (Prop 7.10, 7.17).

**Estimated effort:** ~4-6 weeks. Design doc gets drafted only after v0.6 ships.

---

## Satellite libraries

The "satellite" pattern (decided 2026-05-02 for PolyMarkov, mirrored 2026-05-03 for PolyAggregation): keep Poly.jl core small, delegate domain-specific applications to dedicated packages with one-way dependency `Satellite → Poly.jl`.

### PolyMarkov.jl

**Theme:** Markov-kernel-flavored lenses and dynamical systems — the `MarkovLens <: AbstractLens` extension, stochastic Moore machines, distribution-valued morphism algebra.

**Status:** ready to spin up. The required Poly.jl substrate (`AbstractLens` supertype) shipped in the v0.6 AbstractLens unreleased entry; PolyMarkov can start now.

**Bridge doc:** [`polymarkov_handoff.md`](./polymarkov_handoff.md). Captures the boundary discipline (which types cross, which never do), the sketch of `MarkovLens` operations, and the open Path A vs Path B question for `MarkovLens` ↔ `Lens` interop (which becomes a v0.5.1 polish item if Aidan wants `AbstractLens` ergonomics extended before PolyMarkov spins up).

**Initial seed:** `extensions_v3_design.md` §5.

### PolyAggregation.jl

**Theme:** the §8 aggregation framework — `Schema`, `Instance`, `AggregationFunctor`, `aggregate(inst)` realizing Theorem 8.8 as a homomorphism of left modules in `Cat♯_lin`.

**Status:** v0.2.0 unblocked — the v0.5.1 minimum surface is in `main`. Scaffolding (v0.1.0-DEV — `Schema`, `Instance`, `validate_instance`, the standard `AggregationFunctor` family, and four worked-example skeletons) can drop its v0.5-era stubs and import the real surface now. Gated on v0.7 for **v0.3** (full categorical Theorem 8.8 realization via multi-variable Dirichlet ⊗); v0.6 will broaden the bridge-diagram surface for non-discrete schemas in between.

**Bridge doc:** [`polyaggregation_handoff.md`](./polyaggregation_handoff.md). §1 has the per-version capability gating table (now with v0.5.1 marked shipped); §1.1 documents the two v0.5.1-implementation deviations from the original sketch (`c_one_y` is a c-1 bicomodule, not c-c; `linear_bicomodule_from_span` validates only for discrete bases); §1.2 lists the concrete unblocked actions; §6 has the `Instance` morphism-action representation question (transitions dict vs. comodule wrapper) that PolyAggregation still needs to decide for itself.

**Repo:** placeholder reservation threshold met. Reserve and start the public scaffold whenever you're ready.

---

## Explicitly deferred (no current plan to ship)

- **Niu/Spivak Chapter 5 / Sprint 9** — skipped per 2026-04-27 call.
- **PolyViz Luxor → Makie/GraphMakie/TikzPictures rewrite** — standing todo, separate effort.
- **Catlab.jl deeper integration** — same; v0.6's `Span` struct ships hand-rolled rather than using Catlab's spans.
- **Performance pass on Sprint 8 tree enumeration** — same.
- **Continuous / measure-theoretic versions** of the list polynomial, weak dual, etc. — different category, possibly never.
- **Strong-dual `*-autonomous` structure** on the reflexive subcategory — wrappers + `weak_dual` are sufficient machinery for known consumers.
- **Markov polynomials in Poly.jl core** — lives in PolyMarkov.jl, not here.

---

## Related design docs and references

Design docs (chronological):
- [`historical-design.md`](./historical-design.md) — pre-v0.1 design notes.
- [`extensions_v1_design.md`](./extensions_v1_design.md) — v0.2.0.
- [`extensions_v2_design.md`](./extensions_v2_design.md) — v0.3.0.
- [`extensions_v3_design.md`](./extensions_v3_design.md) — v0.4 carryovers + Markov sketch §5 (PolyMarkov seed).
- [`extensions_v4_design.md`](./extensions_v4_design.md) — v0.6 (Cat♯ inspection + duality bundle).
- [`extensions_v5_design.md`](./extensions_v5_design.md) — v0.5.1 (PolyAggregation minimum-surface patch).

Topic-specific docs:
- [`abstract_lens.md`](./abstract_lens.md) — `AbstractLens` extension contract (v0.6 AbstractLens).
- [`forward_action.md`](./forward_action.md) — v0.4.x + v0.5 forward-action design rationale.
- [`cofree_over_comonoid.md`](./cofree_over_comonoid.md) — cofree comonoid construction notes.
- [`kan_extensions_construction.md`](./kan_extensions_construction.md) — Kan extension implementation notes.
- [`REFERENCES.md`](./REFERENCES.md) — paper / book citations.

Satellite handoffs:
- [`polymarkov_handoff.md`](./polymarkov_handoff.md) — PolyMarkov.jl bridge.
- [`polyaggregation_handoff.md`](./polyaggregation_handoff.md) — PolyAggregation.jl bridge.

---

## Picking up in a new session

If you (or future Aidan, or a collaborator) are picking up in a new session and want to know "what should I work on?", the answer for now is:

1. **Tag housekeeping.** Existing unreleased work in `main` (v0.4, v0.4.x, v0.5, v0.6 AbstractLens, v0.5.1) hasn't been git-tagged yet; last tag is `v0.3.1`; Project.toml is at `0.6.0`. Reconcile in one of two ways:
   - **Option A (cleanest):** roll Project.toml back to `0.5.1`, tag `v0.5.1` cumulatively (covers v0.4 / v0.4.x / v0.5 / v0.5.1), then bump to `0.6.0` and tag `v0.6.0` covering AbstractLens + the v0.6 Cat# inspection bundle once it ships.
   - **Option B (preserve current numbering):** tag intermediate versions (`v0.4.0`, `v0.4.1`, `v0.5.0`, `v0.5.1`) on backdated commits if locatable, then `v0.6.0` once AbstractLens + Cat# inspection both land. More git work; cleaner downstream history.
   - Either way, update the at-a-glance table above when tags catch up. PolyAggregation.jl wants to pin against a tagged Poly version before shipping v0.2.0.
2. **Implement v0.6** per `extensions_v4_design.md`. ~3 weeks. PR order: bridge_diagram → ConjunctiveBicomodule → weak_dual → Kleisli triple → span_from_linear_bicomodule. Resolves no open Qs. Watch for the v0.5.1 c_one_y deviation: when bridge_diagram lands, reconsider whether c_one_y should ship a c-c packaging variant alongside the current c-1 form.
3. **Spin up PolyMarkov.jl** if not blocked on the AbstractLens Path A/B polish item — see `polym