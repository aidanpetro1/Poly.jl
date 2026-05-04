# Poly.jl

[![CI](https://github.com/aidanpetro1/Poly.jl/actions/workflows/CI.yml/badge.svg)](https://github.com/aidanpetro1/Poly.jl/actions/workflows/CI.yml)
[![Docs](https://img.shields.io/badge/docs-stable-blue.svg)](https://aidanpetro1.github.io/Poly.jl/stable/)
[![License: MIT](https://img.shields.io/badge/license-MIT-yellow.svg)](LICENSE)

A Julia library for **polynomial functors** in the categorical sense — `p : Set → Set` of the form `p ≅ Σ_{i ∈ p(1)} y^{p[i]}` — and the categorical machinery built on them: dependent lenses, the four monoidal products, dynamical systems, the Ahman–Uustalu correspondence between comonoids in `(Poly, y, ◁)` and small categories, the cofree comonoid `T_p`, bicomodules, the Cat#-style aggregation primitives, and the Spivak/Garner/Fairbanks coclosure construction.

This library follows two papers in tandem:

- **Niu and Spivak**, *Polynomial Functors: A Mathematical Theory of Interaction* (2024) — the foundational text for chapters 1–8 (polynomials, lenses, monoidal products, dynamical systems, comonoids, cofree comonoid, bicomodules).
- **Spivak, Garner, and Fairbanks**, *Functorial Aggregation* (arXiv 2111.10968v7, 2025) — the Cat# inspection + duality + aggregation framework that drives v0.5.1 onward (`linear_bicomodule_from_span`, `bridge_diagram`, `weak_dual`, `coclosure`, `comonoid_from_coclosure`, `is_reflexive`, the Lemma 8.7 / Fin^op construction).

It is **not** a polynomial-arithmetic library — there are no rings, no GCDs. The objects here model interaction.

## Install

`Poly.jl` is not yet registered in the General registry. Install directly from the repo:

```julia
using Pkg
Pkg.add(url="https://github.com/aidanpetro1/Poly.jl")
```

Or in dev mode for hacking on the library itself:

```julia
Pkg.develop(url="https://github.com/aidanpetro1/Poly.jl")
```

## 30-second example

```julia
using Poly

# A polynomial: y^3 + y, written terse
p = @poly y^3 + y

# A lens by hand: a coin-jar interface (open/closed) over an owner (needy/greedy/content)
q = Polynomial(FinPolySet([:open, :closed]),
               i -> i == :open ? FinPolySet([:penny, :nickel, :dime]) :
                                  FinPolySet(Symbol[]))
owner = Polynomial(FinPolySet([:needy, :greedy, :content]),
                   i -> i == :needy   ? FinPolySet([:save, :spend]) :
                        i == :greedy  ? FinPolySet([:accept, :reject]) :
                                        FinPolySet([:count]))

f = Lens(owner, q,
         i -> i == :content ? :closed : :open,
         (i, coin) -> i == :needy ? (coin == :penny ? :spend : :save) : :accept)

# Apply it as a natural transformation
f(FinPolySet([:x, :y]))((:needy, Dict(:save => :x, :spend => :y)))

# Substitution (`◁` in the book; we use `▷` because Julia rejects `◁`)
(@poly y^2 + 1) ▷ (@poly y^3)        # y^6 + 1

# Cofree comonoid over y+1, depth 2
Tp = cofree_comonoid(@poly y + 1, 2)
validate_comonoid(Tp)                 # true
```

## What's implemented

| Sprint | Topic | Book chapters |
|---|---|---|
| 1 | Cardinalities, `PolySet` hierarchy, `Polynomial`, `apply` | 1–2 |
| 2 | `Lens`, identity, vertical composition, `lens_count`, polybox | 3 |
| 3 | Monoidal products `+`, `×`, `⊗` on polynomials and lenses | 3 |
| 4 | Substitution `▷` (book `◁`) | 6 |
| 5 | Closure `[q, r]`, sections `Γ(p)`, derivative `ṗ`, eval lens | 4 |
| 6 | Dynamical systems `Sy^S → p`, Moore machines, trajectories | 4 |
| 7 | Comonoids = small categories (Cat#), retrofunctors | 7 |
| 8 | Cofree comonoid `T_p` (depth-bounded), comodules, bicomodules | 8 |
| Ext v1 (v0.2) | Lazy `subst`, monoidal ops on `Comonoid`/`Bicomodule`, n-ary `coproduct`, `Coalgebra` peer type, structured `ValidationResult`, `subst_targeted_lens`, symbolic↔concrete interop, lazy `Lens.cod` | 3, 6–8 |
| Ext v2 (v0.3) | `parallel(::Comonoid, ::Comonoid)` carrier-tensor, `BicomoduleMorphism` 2-cells with horizontal composition, Kan extensions (`kan_along_bicomodule` + `kan_2cat` + `KanExtension` record), `support` / `PolyElement` / `free_variables` (Fairbanks Set-sets), `bicomodule_from_data` + `comonoid_from_data`, `back_directions` / `BackDirectionTable` / `sharp_L` / `sharp_R`, `LazyCofreeComonoid`, free-category comonoid builder (later renamed to `free_labeled_transition_comonoid` in v0.3.1), axiom listings + cofree depth-table docs | 3–8 |
| Ext v0.3.x (v0.3.1) | Full Niu/Spivak coequalizer for `compose(::Bicomodule, ::Bicomodule)` (closes v1.1 deferral) + `compose_lazy` / `LazyBicomoduleCarrier`, `validate_bicomodule_composition[_detailed]` with `:M` / `:N` / `:cross` failure attribution, right-Kan extensions (`Π_D` for identity-D and finite non-identity), `free_labeled_transition_comonoid` (supersedes v0.3.0's `free_category_comonoid`, removed in v0.4), `behavior_tree_from_paths`, `parallel(::Comonoid; validate=false)` opt-out, n-ary `parallel` for Comonoid | 8 |
| Ext v3 (v0.4) | Symbolic non-identity `D` for `kan_2cat` (both directions), truly-lazy `LazyBicomoduleCarrier` validator, `cofree_comonoid(::Comonoid, depth)` with universal property + `factor_through`, removal of `free_category_comonoid` shim | 5, 8 |
| v0.4.x | Cat#-completeness bundle: `base_change_left` / `base_change_right`, `cofree_morphism`, `tuple_retrofunctor`, forward-direction action patch for partial-image retrofunctors, `validate_retrofunctor_forward` | 5, 7, 8 |
| v0.5 | `validate_retrofunctor_forward` for partial-image retrofunctors (closes v0.4.x self-validation gap) | 7 |
| v0.6 AbstractLens | `AbstractLens` supertype + accessor protocol (drives PolyMarkov.jl `MarkovLens`) | — |
| v0.5.1 | PolyAggregation minimum surface: `list_polynomial`, `is_linear(::Bicomodule)`, `LinearBicomodule`, `linear_bicomodule_from_span`, `c_one_y`, `morphisms_out_of`, `cod_in_comonoid` | FA §6, §8 |
| v0.6 | PolyAggregation v0.3.0 prereqs: `bridge_diagram`, `weak_dual`, `span_from_linear_bicomodule`, `comonoid_from_list_polynomial` | FA Prop 3.20, Example 7.2, Cor 6.17, Lemma 8.7 |
| v0.6.1 | Paper-faithful Lemma 8.7 + coclosure: `coclosure`, `comonoid_from_coclosure`, `is_reflexive` (replaces v0.6's `comonoid_from_list_polynomial` stub with the right construction on `[u/u]`) | FA Prop 2.16, Example 5.5, Lemma 8.7, Example 7.2 |
| v0.7-partial | Full Prop 3.20 `BridgeDiagram` struct with `(B, E, π, S, T)` data; backward-compatible with v0.6 simplified projection | FA Prop 3.20 |

Plus a parallel symbolic layer (`SymbolicPolynomial`, `SymbolicLens`, ~25 rewrite rules with trace mode), a `@poly` macro, and a LaTeX renderer. Chapter 5 of Niu/Spivak (adjoint quadruple, factorization systems, base change, cartesian closure) is partially implemented in the v0.4.x bundle; the remainder is structural rather than modeling-oriented.

## What's new in v0.7 (in progress)

v0.7-partial shipped 2026-05-04. The full v0.7 round (multi-variable Dirichlet ⊗ on `d-Set[c]`, Theorem 7.19 contravariant equivalence, profunctor↔conjunctive bicomodule dictionary, generalized Kan along bicomodule, duoidality, symbolic coclosure for non-finite carriers) is designed in [`docs/dev/extensions_v6_design.md`](docs/dev/extensions_v6_design.md) and ships across multiple PRs in subsequent rounds.

**v0.7-partial:**

- **`BridgeDiagram` struct** — promotes the v0.6 simplified bridge to the full Spivak/Garner/Fairbanks Prop 3.20 form `(B, E, π, S, T)`. Carries the source bicomodule, position-set `B`, elements-set `E` (pairs `(i, a)`), étale projection `π : E → B`, left leg `S : B → Ob(left_base)`, right leg `T : E → Ob(right_base)`, plus the v0.6 linear-case projection `left_lens` / `right_lens` for backward compat. Constructor is `bridge_diagram(B::Bicomodule)`. Discrete-base case complete; the categorical structure on `E` for general bases ships in v0.7-main PR #7.

## What's new in v0.6.1 (paper-faithful Lemma 8.7 + coclosure)

v0.6.1 followed v0.6 the same day after the FA paper landed in the repo, replacing v0.6's `comonoid_from_list_polynomial` stub with the right construction.

- **`coclosure(q::Polynomial, p::Polynomial)`** — the polynomial `[q/p] = Σ_{i ∈ p(1)} y^{q(p[i])}` from Spivak/Garner/Fairbanks Prop 2.16, equivalently the left Kan extension of `q` along `p` when both are polynomial functors `Set → Set`. Adjunction: `Poly([q/p], p′) ≅ Poly(p, p′ ◁ q)`. Finite case only in v0.6.1; the symbolic / `NatSet` path ships in v0.7-main alongside the multi-var Dirichlet machinery.
- **`comonoid_from_coclosure(p::Polynomial)`** — the natural comonoid on `[p/p]` from FA Example 5.5, the "full internal subcategory spanned by `p`". Eraser picks the identity `(i, id_{p[i]})`; duplicator composes the underlying maps of direction-sets.
- **`comonoid_from_list_polynomial(u)`** — replaces the v0.6 stub with the real FA Lemma 8.7 implementation. Now delegates to `comonoid_from_coclosure(u)`. Requires `list_polynomial(max_size=K)`; presents Fin^op truncated to objects `{0, ..., K}`. The carrier is `[u/u]`, **not** `u` itself — the v0.6 ask conflated `Comon(u) ≃ Fin^op` with `[u/u] ≅ Fin^op`; the latter is what the paper actually states.
- **`is_reflexive(p)`** — FA Example 7.2 predicate: true iff `p` is in the reflexive subcategory where `weak_dual` is invertible (equivalently `is_representable(p) || is_linear(p)`).

## What's new in v0.6 (PolyAggregation v0.3.0 prereqs)

Four additive items extending the v0.5.1 surface for PolyAggregation.jl v0.3.0's parameterized `aggregate_morphism(::Instance)`.

- **`bridge_diagram(B::Bicomodule)`** — extracts the canonical span-shape decomposition of a bicomodule's coactions (FA Prop 3.20). v0.6 returns the linear-case projection `(left_lens, right_lens)`; v0.7-partial promotes to the full `BridgeDiagram` struct.
- **`weak_dual(p::AbstractPolynomial)`** — single-variable Dirichlet weak dual `[p, y]` (FA Example 7.2). Definitionally `internal_hom(p, y)`. Idempotent on the reflexive subcategory generated by `y`, `y^A`, `Ay`. The named alias is the load-bearing call site for the linear↔conjunctive contravariant equivalence (FA Theorem 7.19) shipping in v0.7-main.
- **`span_from_linear_bicomodule(L::LinearBicomodule)`** — reverse direction of v0.5.1's `linear_bicomodule_from_span` (FA Cor 6.17). Returns `(; C, D, S, s, t)`. Round-trips with the forward direction; for `c_one_y(c)` returns the c-1 packaging (`D` = unit comonoid, `t ≡ :pt`).
- **`comonoid_from_list_polynomial(u)`** — v0.6 shipped this as a stub-erroring placeholder; v0.6.1 replaced it with the real FA Lemma 8.7 implementation (see above).

## What's new in v0.5 / v0.5.1 (PolyAggregation surface + retrofunctor validator)

**v0.5** adds `validate_retrofunctor_forward(F)` for retrofunctors built with a partial `forward_on_directions` (e.g. `tuple_retrofunctor` of cofree morphisms). Closes the self-validation gap left by v0.4.x's `base_change_left/right` forward dispatch.

**v0.5.1** ships the Poly.jl-side surface that PolyAggregation.jl v0.1.x / v0.2.0 needs to drop its stubs:

- **`list_polynomial(; max_size=nothing)`** — `u = Σ_{N ∈ ℕ} y^N` (FA Def 8.6). With `max_size`, finite truncation. Without, infinite (`NatSet()` positions).
- **`is_linear(B::Bicomodule)`** + **`LinearBicomodule(B)`** — FA Cor 6.17 / Def 6.4. Predicate-and-wrap for "the carrier is `Sy`" (every direction-set a singleton).
- **`linear_bicomodule_from_span(C, D, S, s, t)`** — FA Cor 6.17 forward direction. Builds `Cy ▷ Sy ◁ Dy` from a span of object-sets.
- **`c_one_y(c::Comonoid)`** — FA Theorem 8.8 carrier as a c-1 bicomodule (right base = unit comonoid). Cod-tracking left action; the c-1 packaging is the natural typing per the paper's framing.
- **`morphisms_out_of(c, a)`** + **`cod_in_comonoid(c, a, f)`** — discoverable wrappers around `direction_at` and `c.duplicator.on_positions` for callers thinking categorically.

The associated **PolyAggregation.jl** library lives separately (per the 2026-05-02 scope decision); see [`docs/dev/polyaggregation_handoff.md`](docs/dev/polyaggregation_handoff.md) for the bridge.

## What's new in v0.4 (Extensions v3 — carryovers)

Closes the four deferrals from v0.3.1 plus the v2 cofree-on-comonoid deferral.

- **Symbolic non-identity `D` for `kan_2cat`.** The symbolic carrier path no longer errors — returns a structurally-typed `KanExtension` with `SymbolicCoequalizer`-positioned extension carrier. New public type `SymbolicCoequalizer <: PolySet`.
- **Truly-lazy `compose_lazy`.** Returns a `Bicomodule` whose carrier `.positions` is a streaming `BicomoduleComposePosSet` rather than a materialized `FinPolySet`. Validators walk it via a new `_iter_positions` polymorphic helper. `Polynomial == Polynomial` now has an identity fast-path.
- **`cofree_comonoid(::Comonoid, depth) -> CofreeOverComonoid`.** The cofree-on-a-comonoid construction. Packages `cofree_comonoid(c.carrier, depth)` with a counit `Retrofunctor : T(c) ⇒ c`. `factor_through(coc, α)` exhibits the universal property element-wise. See [`docs/dev/cofree_over_comonoid.md`](docs/dev/cofree_over_comonoid.md).
- **`free_category_comonoid` removed.** Deprecated in v0.3.1; the BFS / cycle-detection logic is inlined into `free_labeled_transition_comonoid`. **Migration**: swap edge-tuple positions 2 and 3 (`(src, tgt, label)` → `(src, label, tgt)`), rename `max_depth` to `max_path_length`.

Markov polynomials moved to a separate library, **PolyMarkov.jl**, per the 2026-05-02 scope decision. Seed sketch in [`docs/dev/extensions_v3_design.md`](docs/dev/extensions_v3_design.md) §5.

## What was new in v0.3.1 (Concrete Poly v0.3.x asks)

Driven by external feedback from PolyCDS / SOAP-style modeling work. Closes the v1.1-deferred bicomodule-composition coequalizer and ships right-Kan + authoring/validation conveniences:

- **Full Niu/Spivak coequalizer for `compose(::Bicomodule, ::Bicomodule)`.** Carriers are now correct in the general case — positions are coequalizer-balanced pairs `(x, σ)` where `σ : X[x] → Y.positions` matches D-routing, rather than the over-counted `(x, y)` of v0.3.0. `compose_lazy` defers enumeration via `LazyBicomoduleCarrier`. **Required for `master_D = Assessment ⊙ Plan`.**
- **`validate_bicomodule_composition[_detailed](M, N)`** — pre-flight with attributed failures. `location[1] ∈ {:M, :N, :cross}` tells you which operand to fix.
- **Right-Kan extensions** — `kan_along_bicomodule(D, M; direction=:right)` and `kan_2cat(D, F; direction=:right)` ship for identity-D and finite non-identity. `Π_D` unicode alias works on the same surface. **Required for the SOAP audit arm `Π_Plan ∘ Π_Assessment`.**
- **`free_labeled_transition_comonoid(positions, edges; max_path_length)`** — canonical builder for `D` and `P_d` in PolyCDS-style modeling. Edges in `(src, label, tgt)` shape. Supersedes v0.3.0's `free_category_comonoid` (deprecated with `Base.depwarn` in v0.3.1; removed in v0.4).
- **Authoring conveniences** — `behavior_tree_from_paths(label, dict)` for cofree authoring; `parallel(c, d; validate=false)` opt-out; n-ary `parallel(c1, c2, c3, ...)` for Comonoid.
- **Docstring polish** — `bicomodule_from_data` now documents the coverage requirement on `right_back_directions` (and `left_back_directions`) explicitly.

See [`CHANGELOG.md`](CHANGELOG.md) for the full migration notes.

## What was new in v0.3 (Extensions v2)

The v0.3.0 release closed the categorical gaps surfaced by downstream PolyCDS work. Highlights:

- **`BicomoduleMorphism`** — first-class 2-cells in Cat#. Vertical and horizontal composition, whiskering, structural validation matching `validate_bicomodule_detailed`'s failure shape.
- **Kan extensions** — `kan_along_bicomodule` (finite, comodule-along-bicomodule) and `kan_2cat` (symbolic-aware, 2-categorical Kan), both returning a `KanExtension` record with `factor_through` for the universal property. Identity-D case ships in v0.3.0; non-identity (finite) and right-Kan in v0.3.1. See [`docs/dev/kan_extensions_construction.md`](docs/dev/kan_extensions_construction.md).
- **`support` operator** — Fairbanks-style support of `PolyElement(p, position, assignment)` for the concrete case; `free_variables` on `SymExpr` for the symbolic side.
- **Authoring helpers** — `bicomodule_from_data` / `comonoid_from_data` build the underlying lenses from authored Dicts. Validates by default; `validate=false` for intermediate constructions. Walkthrough at [`docs/src/tours/08_bicomodule_walkthrough.md`](docs/src/tours/08_bicomodule_walkthrough.md).
- **`LazyCofreeComonoid`** — defers the tower-of-exponentials `behavior_trees` enumeration. Cached materialization, `tree_at` for single-tree access, lazy `validate_comonoid` via Niu/Spivak Thm 8.45.
- **Inspection** — `back_directions(L::Lens)` returns a `BackDirectionTable` (or callable above `TABULATE_SIZE_CAP`). `sharp_L` / `sharp_R` shorthands for bicomodules; pretty `show` per position groups for fast eyeballing.
- **Soft API break** — `⊗(::Comonoid, ::Comonoid)` is now the carrier-tensor (matching `Polynomial ⊗`); v0.2 callers expecting categorical product should switch to `*`. See [`docs/dev/extensions_v2_design.md`](docs/dev/extensions_v2_design.md) §1.

The full design doc with all 28 resolved questions and the implementation phasing is at [`docs/dev/extensions_v2_design.md`](docs/dev/extensions_v2_design.md).

## Two flavors

The library has two layers that interoperate:

**Concrete layer.** `Polynomial`, `Lens`, etc. — actual data, finite enumeration. Use this when you have explicit position-sets and direction-sets and want to compute. Operations like `subst(p, q)` eagerly enumerate.

**Symbolic layer.** `SymbolicPolynomial`, `SymbolicLens` — variable-driven expression trees with `simplify` and a rewrite-rule engine. Use this when you're working up to isomorphism, want to verify book identities like `(a + b) ⊗ c ≈ (a ⊗ c) + (b ⊗ c)`, or you have non-finite carriers that can't be enumerated.
