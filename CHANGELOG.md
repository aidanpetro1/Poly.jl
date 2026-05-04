# Changelog

All notable changes to Poly.jl. Format follows [Keep a Changelog](https://keepachangelog.com/);
versioning follows [Semantic Versioning](https://semver.org/).

## [Unreleased] — v0.7-partial: full Prop 3.20 bridge + v0.7 design doc (2026-05-04)

> **Headline:** Promotes v0.6's `bridge_diagram` to the paper-faithful
> Prop 3.20 form `(B, E, π, S, T)` as a typed `BridgeDiagram` struct.
> Backward-compatible — `bd.left_lens` / `bd.right_lens` continue to
> resolve to the same lenses. Plus: comprehensive v0.7 design doc
> covering the multi-var Dirichlet stack.

### Added

- **`BridgeDiagram` struct** in `src/CatSharp.jl` carrying the full
  Prop 3.20 data: `bicomodule`, `B` (positions), `E` (elements as a
  set of `(i, a)` tuples), `π : E → B`, `S : B → Ob(left_base)`,
  `T : E → Ob(right_base)`, plus the v0.6 linear-case projection
  `left_lens` / `right_lens` for backward compat.

- **`bridge_diagram(B::Bicomodule)` upgraded** — now returns the
  `BridgeDiagram` struct instead of the v0.6 NamedTuple. Existing v0.6
  call sites (`bd.left_lens`, `bd.right_lens`) continue to work
  unchanged because the struct exposes the same fields.

- **`docs/dev/extensions_v6_design.md`** — focused design doc for the
  v0.7-main pass: multi-variable Dirichlet ⊗ on `d-Set[c]`
  (Lemma 7.13, Cor 7.15), Theorem 7.19 contravariant equivalence,
  profunctor ↔ conjunctive bicomodule dictionary (Prop 7.25, 7.27),
  generalized Kan along bicomodule (Prop 6.7), duoidality (Prop 7.10,
  7.17), symbolic coclosure (extends v0.6.1), and categorical
  structure on `E` in `BridgeDiagram` (Prop 3.20 completion).
  ~25 days estimated implementation effort across 6 PRs.

### Tests

- `test/test_v07_full_bridge.jl` — 5 testsets covering the new
  `BridgeDiagram` struct, v0.6 backward compat, non-linear bicomodule
  E enumeration (`regular_bicomodule(state_system_comonoid)` with
  |E| = |S|² elements), `c_one_y` bridge with the unit-comonoid right
  base, and an error-path placeholder for the symbolic case (deferred
  to v0.7-main).

### Deferred to v0.7-main (see design doc)

The seven items in the v0.7 design doc each warrant their own PR:
multi-var ⊗, Theorem 7.19 duality, profunctor ↔ conjunctive,
generalized Kan, duoidality, symbolic coclosure, and the categorical
structure on `E`. v0.7-partial here ships only the bridge-shape
upgrade.

## [Unreleased] — v0.6.1 paper-faithful Lemma 8.7 + coclosure (2026-05-04)

> **Headline:** Replaces v0.6's `comonoid_from_list_polynomial` stub
> with a paper-faithful implementation after reading the FA paper
> (arXiv 2111.10968v7). The construction was always meant to live on
> the **coclosure** `[u/u]`, not on `u` itself; v0.6.1 ships the
> coclosure operation, the natural comonoid on `[p/p]` (Example 5.5),
> the Lemma 8.7 specialization, and the reflexivity predicate from
> Example 7.2.

### Added

- **`coclosure(q::Polynomial, p::Polynomial)`** in `src/Closure.jl`
  (FA Proposition 2.16 / Niu/Spivak Remark 2.17). The polynomial
  `[q/p] := Σ_{i ∈ p(1)} y^{q(p[i])}`, equivalently the left Kan
  extension of `q` along `p` when both are polynomial functors. Uses
  `apply(q, p[i])` for the direction-set at each position.
  Adjunction: `Poly([q/p], p′) ≅ Poly(p, p′ ◁ q)`. **Finite case
  only** (FinPolySet positions and direction-sets); the symbolic /
  `NatSet` path needed for `coclosure(list_polynomial(),
  list_polynomial())` is deferred to v0.7 alongside the multi-variable
  Dirichlet ⊗ machinery.

- **`comonoid_from_coclosure(p::Polynomial)`** in `src/Comonoid.jl`
  (FA Example 5.5). The natural comonoid on `[p/p]` — the "full
  internal subcategory spanned by `p`" — with eraser picking the
  identity `(i, id_{p[i]})` at each position and duplicator on
  directions composing the underlying maps of direction-sets.
  Validates as a comonoid for any finite `p`. Builds the duplicator
  via `subst_targeted_lens` to keep the codomain lazy.

- **`is_reflexive(p::Polynomial)`** in `src/Polynomial.jl` (FA
  Example 7.2). Predicate: true iff `p` is in the reflexive
  subcategory where `weak_dual` is invertible — equivalently
  `is_representable(p) || is_linear(p)`. Useful as a pre-check for
  callers wanting `weak_dual(weak_dual(p)) ≅ p` to hold.

### Changed

- **`comonoid_from_list_polynomial(u)`** in `src/Demos.jl` —
  replaced the v0.6 stub with the real FA Lemma 8.7 implementation.
  Now delegates to `comonoid_from_coclosure(u)`. Requires `u` to be a
  finite truncation `list_polynomial(max_size=K)` (the unbounded form
  with `NatSet` positions errors clearly, deferring to v0.7's
  symbolic-positions pass). The resulting comonoid presents Fin^op
  restricted to objects `{0, ..., K}` — Lemma 8.7 verbatim. The
  function name is preserved per the v0.6 ask, but the carrier is
  `[u/u]`, NOT `u` itself; the docstring spells this out.

- **`bridge_diagram` docstring** annotated with FA Prop 3.20 framing —
  the v0.6 implementation is the **linear-case projection** of the
  full Prop 3.20 bridge `(B, E, π, S, T)`, correct for linear
  bicomodules where the étale fibers are singletons but lossy for
  general bicomodules. The full bridge ships in v0.7.

### Tests

- `test/test_v061_coclosure.jl` — four testsets covering
  `coclosure(q, p)` (basic shape + Example 2.18 lens reduction +
  rejection of non-finite operands), `comonoid_from_coclosure`
  (Example 5.5 morphism counts + identity check on `y + y²`),
  `comonoid_from_list_polynomial` (Lemma 8.7 / Fin^op truncation
  morphism counts + composition + alias agreement), and `is_reflexive`
  (Example 7.2 cases + idempotence of weak_dual on reflexive subcat).

### Paper cross-references locked in

After reading FA arXiv 2111.10968v7, the v0.6 work checks out paper-
faithful with one annotation:

  - **`weak_dual(p)`** (v0.6, `Monoidal.jl`) — Example 7.2 confirms
    `p^∨ = [p, y] = Σ_{f ∈ Π p[i]} y^{p(1)}`, exactly what
    `internal_hom(p, y)` returns. The "positions are functions
    `p(1) → p(1)`" sketch in the original v0.6 ask was incorrect and
    has been retracted in the docstring.
  - **`span_from_linear_bicomodule`** (v0.6, `CatSharp.jl`) — Cor 6.17
    discrete-base reverse direction, paper-faithful as shipped.
  - **`bridge_diagram`** (v0.6, `CatSharp.jl`) — annotated as the
    linear-case projection of Prop 3.20; full version deferred.

## [Unreleased] — v0.6 PolyAggregation v0.3.0 prereqs (2026-05-04)

> **Headline:** Three of four v0.6 PolyAggregation v0.3.0 prereqs land
> additively; the fourth ships as a documented stub pending design
> resolution.

Filed by Aidan as the 2026-05-04 PR ask, after PolyAggregation v0.2.0
shipped against the v0.5.1 surface. Four items intended to support
PolyAggregation v0.3.0's parameterized `aggregate_morphism(::Instance)`
constructor and round out the linear/conjunctive duality picture. As
with the v0.5.1 round, no breaking changes; the bigger v0.7 work
(multi-variable Dirichlet ⊗ on `d-Set[c]`) remains deferred.

### Added

- **`bridge_diagram(B::Bicomodule)`** in `src/CatSharp.jl` (Prop 3.20).
  Returns a `NamedTuple` `(; left_lens, right_lens)` extracting the
  canonical span-shape decomposition of `B`'s carrier into a left-leg
  lens `B.carrier → B.left_base.carrier` and a right-leg lens
  `B.carrier → B.right_base.carrier`. The on-direction callbacks pick
  the canonical `b = first(carrier[x].elements)` direction for the
  substitution-shape lookup — well-defined and unique on linear
  bicomodules; surfaces a clear error on positions with empty
  direction-sets. Structural primitive used by PolyAggregation v0.3.0's
  `aggregate_morphism` row-routing on directions.

- **`span_from_linear_bicomodule(L::LinearBicomodule)`** in
  `src/CatSharp.jl` (Cor 6.17 reverse direction). Returns
  `(; C, D, S, s, t)` recovering the span data from a linear
  bicomodule. Round-trips with v0.5.1's `linear_bicomodule_from_span`:
  `span_from_linear_bicomodule(linear_bicomodule_from_span(C, D, S, s,
  t))` returns extensionally-equal `s, t` for every `x ∈ S`. For
  `c_one_y(c)` returns the c-1 packaging (`D` = unit comonoid, `t` ≡
  `:pt`). Promotes PolyAggregation's private `_query_source` /
  `_query_target` accessors to a public Poly API.

- **`weak_dual(p::AbstractPolynomial)`** in `src/Monoidal.jl` (Niu/Spivak
  Prop 4.85 / Spivak/Garner/Fairbanks Theorem 7.19 alias).
  Definitionally `internal_hom(p, y)` — the single-variable Dirichlet
  weak dual `[p, y]`, i.e., the closure of `⊗` evaluated against the
  unit. The named alias is reserved for the linear ↔ conjunctive
  contravariant equivalence treatment that lands fully in v0.7.
  Satisfies Niu/Spivak Example 4.81 identities (`[Iy, y] ≅ y^I` and
  `[y^I, y] ≅ Iy`) and is idempotent on the reflexive subcategory
  generated by `y, y^A, Ay, ...`. Note: `weak_dual(constant(I)) ≅
  zero_poly` for non-empty `I` — `constant`s sit outside the reflexive
  subcategory; documented in the docstring's "Caveats" section.

### Stubbed (pending design resolution)

- **`comonoid_from_list_polynomial(u::AbstractPolynomial)`** in
  `src/Demos.jl` (Def 8.6 second half). Reserved entry point for the
  comonoid structure on the list polynomial; **not yet implemented**.
  Two sub-issues block a paper-faithful implementation against the
  v0.5.1 carrier shape: (1) `direction_at(u, 0)` is empty, precluding a
  well-formed eraser `Lens u → y` at N=0; (2) the Spivak/Garner/Fairbanks
  iso `[u/u] ≅ Fin^op` is on the **coclosure** `[u/u]`, not on the
  comonoid carrier `u` itself. The function exists as an exported
  symbol so PolyAggregation v0.3.0 can `using Poly:
  comonoid_from_list_polynomial` without breaking; calling it raises a
  clear error pointing at three resolution paths (re-shape carrier,
  restrict to N≥1, or defer to v0.7) documented in `src/Demos.jl` and
  `docs/dev/extensions_v4_design.md §4`. PolyAggregation v0.3.0's
  hand-rolled simple-shape `aggregate_morphism` cases don't need this
  constructor — the parameterized version that does need it ships when
  this function does.

### Deferred to v0.6 follow-up (not blocking PolyAggregation v0.3.0)

- `is_conjunctive(B)` + `ConjunctiveBicomodule(B)` (Cor 6.15).
- `Span{A,B}` struct + finite-set pullback in `compose(::Span, ::Span)`
  + convenience constructor `linear_bicomodule_from_span(span)`.

### Tests

- `test/test_v06_polyaggregation_v030_prereqs.jl` — four testsets:
  `span_from_linear_bicomodule` (round-trip + c_one_y + error path),
  `bridge_diagram` (linear-bicomodule recovery + discrete projections +
  c_one_y + cross-check with span recovery), `weak_dual` (Example 4.81
  identities + idempotence on reflexive subcat + alias check + constant
  caveat), and `comonoid_from_list_polynomial (stub)` (error path +
  symbol resolution).

## [Unreleased] — v0.5.1 PolyAggregation minimum surface (2026-05-03)

> **Headline:** Minimum surface for PolyAggregation.jl v0.1.x.

Five additive items so PolyAggregation.jl v0.1.x can drop its stubs and ship
a working data-level `aggregate(::Instance)`. Designed as a patch release on
top of the shipping v0.5; no breaking changes; no new dependencies. Per
`docs/dev/extensions_v5_design.md`, this lands ahead of the broader v0.6
Cat# inspection bundle. (Intended release ordering: v0.5 → v0.5.1 → v0.6;
the Project.toml currently reads `0.6.0` reflecting cumulative untagged
work. Aidan's separate version-numbering reconciliation across v0.4,
v0.4.x, v0.5, v0.5.1, and v0.6 AbstractLens is tracked in ROADMAP.md.)

### Added

- **`list_polynomial(; max_size::Union{Int,Nothing}=nothing)`** in
  `src/Demos.jl`. The list polynomial `u = Σ_{N ∈ ℕ} y^N` of
  Spivak/Garner/Fairbanks Def 8.6 — carrier of the universal aggregator.
  Without `max_size`: positions is `NatSet()`. With `max_size = K`:
  positions is `FinPolySet(0:K)`. Direction-set at position `N` is
  `FinPolySet(1:N)` in both modes. The Kleisli triple `(u, η, μ)` and
  `comonoid_from_list_polynomial` ship in v0.6.

- **`is_linear(B::Bicomodule)`** in new `src/CatSharp.jl` (Def 6.4 / Cor
  6.17). Predicate: every position of `B.carrier` has direction-set of
  size 1 — equivalently, the carrier is `Sy`. Coexists with the existing
  `is_linear(::AbstractPolynomial)` predicate via multiple dispatch.
  Conservatively returns `false` for non-finite carrier-positions; the
  fuller bridge-diagram path lands in v0.6.

- **`LinearBicomodule(B::Bicomodule)`** in `src/CatSharp.jl`. Typed
  validate-and-wrap tag asserting `is_linear(B)`. Never mutates or
  normalizes the underlying bicomodule. Symmetric to v0.6's
  `ConjunctiveBicomodule`.

- **`linear_bicomodule_from_span(C, D, S, s, t; validate=true)`** in
  `src/CatSharp.jl` (Cor 6.17 forward direction). Builds the linear
  bicomodule `Cy ▷ Sy ◁ Dy` corresponding to a span
  `Ob(C) ←ˢ S →ᵗ Ob(D)`. Validates that `s(x) ∈ Ob(C)` and `t(x) ∈ Ob(D)`
  for every `x ∈ S` when `validate=true`. The reverse direction
  `span_from_linear_bicomodule`, the `Span{A,B}` struct, the finite-set
  pullback in `compose(::Span, ::Span)`, and the convenience constructor
  `linear_bicomodule_from_span(span)` ship in v0.6.

- **`c_one_y(c::Comonoid)`** in `src/CatSharp.jl` (Theorem 8.8 carrier).
  The linear bicomodule `c(1)y` viewed as a self-bicomodule
  `c ▷ c(1)y ◁ c`. Both coactions use the trivial action: morphisms of
  `c` are forgotten on the direction side; only object-tags propagate.
  Equivalent to `linear_bicomodule_from_span(c, c, positions(c.carrier),
  identity, identity)`, factored out as a named function because every
  PolyAggregation call site that needs `c(1)y` would otherwise build it
  with this 6-line literal.

- **`morphisms_out_of(c::Comonoid, a)`** and
  **`cod_in_comonoid(c::Comonoid, a, f)`** in `src/Comonoid.jl` (pure
  ergonomics). Wrappers around `direction_at(c.carrier, a)` and
  `c.duplicator.on_positions.f(a)` for callers thinking in categorical
  terms ("morphisms out of `a`", "codomain of `f`") rather than
  polynomial-level plumbing. Pure renames of existing API; no new
  behavior.

### Tests

- New `test/test_v051_polyaggregation_surface.jl` — five testsets
  covering each of the items above against `discrete_comonoid`,
  `state_system_comonoid`, and `free_labeled_transition_comonoid` from
  the existing comonoid families.

### Notes / forward pointers

- **v0.6 (next release).** Extends `src/CatSharp.jl` with
  `bridge_diagram(::Bicomodule)` + `BridgeDiagram` struct (Prop 3.20),
  `is_conjunctive` + `ConjunctiveBicomodule` (Cor 6.15), and the
  reverse-span machinery (`Span{A,B}` struct, finite-set pullback in
  `compose(::Span, ::Span)`, `span_from_linear_bicomodule`, convenience
  `linear_bicomodule_from_span(span)`). Extends `src/Monoidal.jl` with
  `weak_dual(p)` and `is_reflexive(p; depth=2)` (Example 7.2,
  single-var Dirichlet). Extends `src/Demos.jl` with the Kleisli triple
  `(u, η, μ)` for `list_polynomial` and `comonoid_from_list_polynomial`.

- **v0.7 (round that unblocks PolyAggregation v0.3 / Theorem 8.8 full
  realization).** Multi-variable Dirichlet ⊗ on `d-Set[c]` (paper
  §7.2-7.3, Lemma 7.13, Cor 7.15), Theorem 7.19 contravariant
  equivalence `Cat#_lin ↔ Cat#_disc,con`, profunctor ↔ conjunctive
  bicomodule dictionary (§7.3.1, Prop 7.25), generalize
  `kan_along_bicomodule` to general `(c, d)` (Prop 6.7), duoidality
  natural map `(p ◁ q) ⊗ (p' ◁ q') → (p ⊗ p') ◁ (q ⊗ q')` (Prop 7.10,
  7.17).

## [Unreleased] — v0.6 AbstractLens (2026-05-03)

### Added

- **`AbstractLens` supertype** — abstract supertype for lens
  representations, mirroring the `AbstractPolynomial` pattern. `Lens
  <: AbstractLens`. Enables PolyMarkov.jl's `MarkovLens` and other
  future lens variants to participate in a documented interface.
- **Accessors `dom`, `cod`, `on_positions`, `on_directions`,
  `is_deterministic`** on `AbstractLens`. Default implementations on
  `Lens` return field values; additive on top of direct field access,
  no breaking change.
- **`docs/dev/abstract_lens.md`** documenting the extension contract:
  what subtypes must implement, what they do NOT inherit, the
  `to_lens` / `to_<subtype>` coercion convention, and field-access
  vs. accessor guidance.
- **`examples/abstract_lens_minimum_viable.jl`** — worked-example
  `IdentityLensWrapper <: AbstractLens` exercising the contract end-
  to-end (authored as a `.jl` script to match the existing examples
  convention; cells lift directly into a Pluto session).

### Tests

- New `test/test_v06_abstract_lens.jl`: supertype membership, accessor
  identity-vs-fields, `is_deterministic` on identity / eraser /
  duplicator, backward-compat smoke tests for `Lens`-typed
  constructors.

### Notes

- Method bodies of `compose`, `parallel`, `subst`, `*`, `+`, `▷`, `⊙`,
  `back_directions`, `polybox`, `lift`, etc. intentionally remain
  typed `::Lens`. Subtypes declare their own methods on their own
  type. Mixed-type calls require explicit conversion. See
  `docs/dev/abstract_lens.md`.
- `Lens.cod`-as-`AbstractPolynomial` widening (v0.4.x lazy sweep) and
  `forward_on_directions` (v0.4.x) are unchanged by this work.

## [Unreleased] — v0.5 forward-action validator (2026-05-03)

### Added

- **`validate_retrofunctor_forward(F)` / `validate_retrofunctor_forward_detailed(F)`** — companion to the v0.4.x `forward_on_directions` patch (`base_change_left/right` dispatch), addressing the symmetric self-validation gap. Source: PolyCDS v1.7 iso-test continuation.

  `validate_retrofunctor(F; strict=true|false)` evaluates `F.underlying.on_directions` on every cod-direction and errors on partial-image retrofunctors — `tuple_retrofunctor`'s agreement check throws on non-image direction tuples. The new validator iterates dom-directions and uses `F.forward_on_directions` exclusively, never touching `on_directions`.

  **What it checks (counit + composition law):**

  - Counit: `F.forward(c0).f(id_dom_at_c0) == id_cod_at_F(c0)`.
  - Composition law: `F.forward(c0).f(b ;_dom b') == F.forward(c0).f(b) ;_cod F.forward(c0').f(b')`. For cofree comonoids this reads "forward respects path concatenation" — exactly the invariant of `cofree_morphism`'s filter-subsequence and `tuple_retrofunctor`'s componentwise pack.

  **What it deliberately does NOT check (position-side comult):** the equation `F(c0') ?= jbar_cod(F(c0))[F.forward(c0).f(b)]` fails on `cofree_morphism(L, depth)` over a non-identity L (which strict-validates as a back-action retrofunctor, per its docstring). When `b` is a dom-direction outside `L`'s image, the filter sends it to identity `()`, whose cod-codomain is `F(c0)` itself — but `F(c0')` is a strictly deeper subtree. Forward and back-action carry *different* information for partial-image cases (`F♯ ∘ F.forward ≠ id`), so position-side is not an invariant of valid retrofunctors. Counit + composition is.

  **Strictly weaker contract than `validate_retrofunctor`:** the back-action validator verifies `F.underlying` is a strict comonoid morphism; the forward validator verifies `F.forward` is a compositional map of morphism algebras. Both can pass for the same F (identity, single cofree_morphism). Only forward passes for partial-image cases (boundary tuple_retrofunctor of cofree_morphism over distinct alphabet inclusions). Use whichever matches the audit you want.

  **Dispatch convention** mirrors `base_change_left`'s forward-action patch: presence of `forward_on_directions` selects the forward path. Same architectural seam, different consumer surface.

### Tests

- New `test/test_v04x_validate_retrofunctor_forward.jl` (6 testsets): partial-image tuple_retrofunctor (forward passes, both strict and element-wise back-action error), cofree_morphism alone over alphabet inclusion at depth 2 (both validators pass — exercises non-trivial composition where filter drops directions mid-path), identity_retrofunctor (forward + strict both pass), error when `forward_on_directions === nothing`, `_detailed` returns `ValidationResult` with `.passed`/`.failures`, verbose modes don't throw.

### Documentation

- New `docs/dev/forward_action.md` collecting the v0.4.x + v0.5 forward-action design rationale, "which validator when" table, and the dispatch convention. Pairs with the existing `forward_on_directions` field docstring on `Retrofunctor`.
- Carve-out paragraph added to `validate_retrofunctor`'s docstring (Comonoid.jl), pointing partial-image users to `validate_retrofunctor_forward`. Parallel to the existing `cofree_universal` carve-out.

## [Unreleased] — v0.4.x forward-direction action patch (2026-05-02)

### Added

- **`Retrofunctor.forward_on_directions`** — optional forward-direction action on retrofunctors. Source: PolyCDS deep-modularity follow-up to the Cat#-completeness bundle.

  A retrofunctor `F : C → D` always carries the back-action on directions (in `underlying.on_directions`); the new field exposes the symmetric forward action when the constructor can compute it. API is curried: `F.forward_on_directions(c0_pos).f(b_0)` returns the cod-direction at `F(c0_pos)` corresponding to dom-direction `b_0`. The inner value is a NamedTuple `(; f = closure)` — lightweight wrapper supporting `.f` access without `PolyFunction`'s dom/cod construction overhead.

  Populated canonically by:

  - **`identity_retrofunctor(c)`** — forward = identity on directions.
  - **`compose(F, G)`** — propagates forward when both have it; `nothing` otherwise.
  - **`cofree_morphism(L, depth)`** — forward = filter-subsequence. At each step in the dom-tree-path, look up if the p-direction is in the image of `L.on_directions(cur_q_label)`; if yes, append the corresponding q-direction; if no, skip (q-path gets shorter). Total on every dom-direction; image at a tensored cod is a proper subset when `L`'s back-action is non-surjective.
  - **`tuple_retrofunctor(Fs)`** — forward = per-component tuple in the left-fold nesting. Set iff every `F_d` carries forward.

- **Forward-iteration variants in `base_change_left` / `base_change_right`** — when `F.forward_on_directions !== nothing`, dispatch to internal `_base_change_left_forward` / `_base_change_right_forward`. These iterate dom-directions forward and apply the canonical forward action directly, skipping the F-on-directions injectivity check (irrelevant when not inverting). Position-injectivity preconditions kept ("same as backward" per spec).

  Use case: PolyCDS's boundary `f : cofree(y^Σ) → ⊗_d cofree(y^{Σ_d})` constructed via `tuple_retrofunctor([cofree_morphism(L_d, depth) for d])`. Its image is a proper subcategory of the codomain — at the tensored tree-position, the image has 13 morphisms vs. 49 for the full categorical product. The 36 non-image direction-tuples can't be lifted to any C-direction (no single Σ-tree-path γ satisfies `filter_d(γ) = b_d` for all d simultaneously). The backward path's `tuple_retrofunctor` agreement check throws on these; the forward path never touches them.

  Backward-compatible: existing 3-arg `Retrofunctor(dom, cod, underlying)` callers leave the field `nothing` and hit the existing backward path. The kwarg-only constructor signature means no positional breakage.

### Tests

- New `test/test_v04x_forward_action.jl` (52 testcases): field plumbing, identity/compose/cofree_morphism/tuple_retrofunctor population, boundary forward-totality across all dom-directions, identity-G `base_change_right`, no-forward-Retrofunctor backward-compat path.

### Notes / deferred

- Forward action populated only by `cofree_morphism` and `tuple_retrofunctor`. `cofree_universal` and `cofree_comonoid(::Comonoid, depth)`'s counit don't populate it (could be added if PolyCDS needs partial-image versions of those).
- End-to-end `base_change_left(boundary, AP_tensored)` succeeding on the PolyCDS use case requires `AP_tensored` to be position-compatible with the boundary's image (its left-coaction's image must stay inside `boundary.on_positions`'s image). PolyCDS's actual `AP_tensored` is built with that constraint; `regular_bicomodule(boundary.cod)` doesn't satisfy it. The forward-totality test in this release verifies the patch's substantive content; PolyCDS verifies the integration.

### Fixed (perf, 2026-05-02)

- **`subst_targeted_lens` now uses `subst_lazy`** instead of eager `subst(p, q)` for its codomain (`src/Monoidal.jl`). This is the natural completion of the v0.4.0 lazy-everywhere sweep — same pattern as the cofree-comonoid duplicator fix, applied to the remaining call site that was constructing a derived-lens cod via eager `subst`. The v0.2 design doc deferred this on grounds that `Lens.cod` had to be `ConcretePolynomial`; that constraint was lifted later (Lens.cod is now `AbstractPolynomial`), so the swap is now a one-line change.

  Surfaced by PolyCDS's `compile_protocols_to_soap` in the deep-modularity refactor: `_base_change_left_forward(F, M)` calls `subst_targeted_lens(M.carrier, C0, M.carrier, …)`. On the toy 2-disease fixture (`M.carrier` ≈ 25 positions with ~9 directions per position, `C0` = `cofree(y^Σ, 1).carrier`), eager `subst(C0, M.carrier)` would build `Σ_x Π_a |M.carrier[a]|` ≈ `25^9 ≈ 4·10^12` jbar dictionaries, hanging Julia mid-`Dict` construction at module load. With `subst_lazy`, construction returns immediately; downstream consumers shape-check the cod via `is_subst_of`, which short-circuits on `LazySubst`.

  Backward-compat: `Lens` cross-type `==(LazySubst, ConcretePolynomial)` (Monoidal.jl) keeps the existing `f.cod == subst(p, q)` invariant in `test_extensions_subst_targeted.jl` working — the cross-type `==` materializes the lazy side once for comparison only. The v0.4.x `base_change_left/right` paths and the v0.4.0 cofree work were already lazy-cod aware.

### Tests

- New `test/test_v04x_lazy_subst_targeted.jl` (7 testsets): structural `LazySubst` cod check; non-materialization on a `5^10`-position would-be-eager fixture; `is_subst_of` short-circuit; cross-type `==` backward-compat; `subst_targeted_coaction` propagation on both `:left` and `:right` sides; end-to-end `Bicomodule` constructor smoke test; behavioral equivalence vs. the manual eager build.

## [0.4.0] — Extensions v3 (carryovers)

### Added (post-spec PolyCDS asks, 2026-05-02)

- **Cat#-completeness operations bundle** (#5):

  - **`base_change_left(F::Retrofunctor, M::Bicomodule)`** — restrict `M : F.cod ⇸ D` along `F : F.dom → F.cod` to produce `F* M : F.dom ⇸ D`. The Cat# vertical-on-horizontal action; companion to `parallel(::Bicomodule, ::Bicomodule)`.
  - **`base_change_right(M::Bicomodule, G::Retrofunctor)`** — symmetric to `base_change_left`, on the right base.
  - **`cofree_morphism(L::Lens, depth::Int) -> Retrofunctor`** — functorial action of cofree on polynomial morphisms. Given `L : p → q`, returns the induced retrofunctor `cofree_comonoid(p, depth) → cofree_comonoid(q, depth)`. Distinct from `cofree_universal` (which solves the labeling-factorization universal property).
  - **`tuple_retrofunctor(Fs::Vector{Retrofunctor}; validate=true)`** — universal arrow into a carrier-tensor of comonoids. Given retrofunctors `F_d : C → D_d` sharing the same domain, returns `⟨F_d⟩ : C → ⊗_d D_d`. The `validate=true` default checks that per-component direction lifts agree (compatibility); pass `false` for hot paths.

  Bundle motivation: PolyCDS's deep-modularity refactor needs to compose an alphabet-inclusion comonoid morphism with a tensored bicomodule. With base-change ops the composition lands in bicomodule-land cleanly; with `cofree_morphism` + `tuple_retrofunctor` the boundary morphism is *derived* from per-disease alphabet inclusions instead of hand-rolled, so it strict-validates.

  **Direction-of-subst design note** (re-stated for the bundle): the user's suggested bodies for `base_change_left/right` composed with `subst(F.underlying, identity_lens(...))`, assuming `subst(::Lens, ::Lens)` is contravariant in the first argument. In Poly.jl `subst(f, g)` is **covariant in both arguments** (see `Monoidal.jl`), so the direct compose doesn't typecheck. Both `base_change_left/right` build the new coaction explicitly via `subst_targeted_lens` with position- and direction-preimage lookups. Works whenever `F`/`G` is injective on positions in the relevant image and on directions at each preimage; errors clearly otherwise.

  **Tuple-shape note** for `tuple_retrofunctor`: `reduce(_comonoid_carrier_tensor, …)` left-folds, so positions and directions in the tensored cod are nested left-fold tuples (`((p_1, p_2), p_3)` for n=3, etc.). The on-positions / on-directions functions construct and decompose with that nesting in mind.

### Fixed (perf, 2026-05-02)

- **`cofree_comonoid(::Polynomial, depth)` duplicator now uses `subst_lazy`** instead of eager `subst(carrier, carrier)` for the duplicator's codomain. The eager form materialized `Σ_t |q(1)|^|t-paths|` jbar dictionaries to construct the codomain — for cofree on a representable `y^{a,b,c}` at depth 2, the depth-2 tree has 13 paths and `q.positions = 3`, so `3^13 ≈ 1.59 million` jbars were built just for the codomain. Pure waste, since downstream code only ever shape-checks the codomain via `is_subst_of`, which short-circuits on `LazySubst` immediately. Fix: change `subst` to `subst_lazy`. The v0.4.x bundle test went from 7m52s / 122 GB allocations to a normal runtime; the existing v0.3 cofree tests speed up for the same reason. Latent bug since v0.3 — surfaced by the v0.4.x #5 `cofree_morphism` tests which build cofrees at depth 2 on representable `y^X`.



Closes the four deferrals from v0.3.1 and the v2 `cofree-on-comonoid`
deferral (#13). Markov polynomials moved to a separate library
(PolyMarkov.jl) per the 2026-05-02 scope decision; not in this release.

### Added

- **Symbolic non-identity `D` for `kan_2cat`** (#1, both directions).
  `kan_2cat(D, F; direction)` now accepts symbolic carriers (any
  non-`FinPolySet` positions on `D` or `F`) and returns a structurally-
  typed `KanExtension` whose extension bicomodule has
  `SymbolicCoequalizer` positions and `SymbolicSet` direction-sets.
  Coactions use `subst_lazy` codomains so the bicomodule constructor's
  `is_subst_of` check passes via the lazy short-circuit. The
  unit/counit `BicomoduleMorphism` and the result of `factor_through`
  carry placeholder lens functions that error if invoked at concrete
  elements — symbolic results are structural by design. See
  `docs/dev/extensions_v3_design.md` §1 and `docs/dev/kan_extensions_construction.md`.
- **`SymbolicCoequalizer <: PolySet`** — a symbolic representation of a
  quotient set `parent / ~`, with a `relation::Vector{Tuple{Any,Any}}`
  list of generating equations. Used by the symbolic `kan_2cat` path;
  available as a public type for user code that needs the same shape.
- **Truly-lazy `LazyBicomoduleCarrier` and `compose_lazy`** (#2).
  `compose_lazy(M, N)` now returns a `Bicomodule` whose carrier
  `.positions` is a streaming `BicomoduleComposePosSet`, not a
  materialized `FinPolySet`. The structural cardinality formula
  `Σ_x Π_a #compatible_y(a)` runs without enumeration.
  `validate_bicomodule_detailed` and the underlying right/left-comodule
  validators accept the streaming form via a new internal
  `_iter_positions` polymorphic helper. Validation memory drops from
  O(|M ⊙ N positions|) Polynomial materialization to O(|N.positions|)
  for the once-per-iteration `y_by_d` index.
- **`cofree_comonoid(::Comonoid, depth) -> CofreeOverComonoid`** (#4).
  The depth-bounded cofree-on-a-comonoid. Distinct from
  `cofree_comonoid(::Polynomial, depth)`; packages the underlying tree
  comonoid with a counit `Retrofunctor : T(c) ⇒ c`.
  `factor_through(coc, α)` exhibits the universal property
  element-wise (Q4.2 default `strict=false`), delegating to
  `cofree_universal` under the hood. Companion design note at
  `docs/dev/cofree_over_comonoid.md`.
- **`Polynomial == Polynomial` identity fast-path.** Two identical
  Polynomial objects (`p === q`) now return `true` from `==` without
  iterating. For non-`FinPolySet` positions, the comparison falls back
  to identity-via-`===` on the `direction_at` function rather than
  erroring. Required for the truly-lazy compose path (lens / comodule
  constructors check `coaction.dom == carrier` where both are the same
  Polynomial object).

### Removed

- **`free_category_comonoid` deprecation shim** (#3). v0.3.1 deprecated
  this in favor of `free_labeled_transition_comonoid` with a
  `Base.depwarn` forwarder; v0.4 removes the shim entirely. The BFS /
  cycle-detection logic is inlined into `free_labeled_transition_comonoid`.

  **Migration**: change `free_category_comonoid(vertices, edges; max_depth)`
  with `(src, tgt)` or `(src, tgt, label)` edges to
  `free_labeled_transition_comonoid(positions, edges; max_path_length)`
  with `(src, label, tgt)` edges. Edge-tuple positions 2 and 3 swap;
  `max_depth` renames to `max_path_length`.

### Changed

- The v2 test file `test_extensions_v2_free_category.jl` is retired
  (the function it tested is gone). Its successor coverage lives in
  `test_v04_free_labeled_transition.jl`. The retired file remains as a
  one-line stub for one minor; safe to delete in v0.5.

### Deferred

- **PolyMarkov.jl** — Markov polynomials, distributions, MarkovLens,
  MarkovComonoid, MarkovDynamicalSystem. Moved to a separate library
  per the 2026-05-02 scope decision. The seed sketch lives in
  `docs/dev/extensions_v3_design.md` §5.
- **Lazy cofree-on-a-comonoid** — mirror of v2 #8 for the new
  `CofreeOverComonoid` type. Defer until modeling work needs it.

## [0.3.1] — Concrete Poly v0.3.x asks

Driven by external feedback on v0.3.0 from PolyCDS / SOAP-modeling
work. Closes the v1.1-deferred bicomodule-composition coequalizer,
ships right-Kan, and adds authoring + validation conveniences.

### Added

- **Full Niu/Spivak coequalizer for `compose(::Bicomodule, ::Bicomodule)`.**
  Carrier positions are now coequalizer-balanced pairs `(x, σ)` where
  `σ : X[x] → Y.positions` matches the D-routing on both sides:

      λ_L^N(σ(a)).first  ==  mbar_R^M(x)(a)   for every a ∈ X[x].

  This generalizes the previous regular-bicomodule approximation. For
  direction-sets `M.carrier[x]` of cardinality `> 1` the new
  construction correctly produces `Π_a #compatible_y(a)` positions per
  `x` rather than the over-counted `|M.carrier[x]| × #compatible_y` of
  the old impl. Closes the v1.1 deferral. Required for the SOAP
  factoring pattern `master_D = Assessment ⊙ Plan` and downstream code
  paths needing the master bicomodule recovery.
- **`compose_lazy(M, N)` and `LazyBicomoduleCarrier`** — lazy variant of
  `compose` whose carrier defers position enumeration. Use when the
  eager `Π_a #compatible_y(a)` count would be too large.
- **`validate_bicomodule_composition[_detailed](M, N)`** — pre-flight
  check for `compose(M, N)` with attributed failure information. Each
  failure's `location[1]` is one of `:M`, `:N`, or `:cross`, indicating
  which operand to investigate. Use as a guard before bicomodule
  composition in pipelines where M/N originate independently.
- **Right-Kan extensions (`Π_D`).** `kan_along_bicomodule(D, M; direction=:right)`
  ships for both the identity-D case (ε = id, extension ≅ M) and
  finite non-identity D (dual section construction). `kan_2cat(D, F;
  direction=:right)` mirrors the symbolic-aware left-Kan path:
  identity-D and finite non-identity ship; symbolic non-identity rolls
  into v0.4. `Π_D` unicode alias works on the same surface.
  `factor_through(k, α)` extended to handle right-direction Kan
  extensions and non-identity D for finite carriers. Required for the
  SOAP audit arm `Π_Plan ∘ Π_Assessment`.
- **`free_labeled_transition_comonoid(positions, edges; max_path_length)`**
  — canonical builder for D and P_d in PolyCDS-style modeling. Edges
  in `(src, label, tgt)` shape (labeled transition system convention);
  `(src, tgt)` two-tuple also accepted with auto-label. Supersedes
  v0.3.0's `free_category_comonoid`.
- **`behavior_tree_from_paths(label_at_root, paths)`** — convenience
  constructor for `BehaviorTree` taking a flat `path → label` Dict
  rather than nested children Dicts. Mirrors `bicomodule_from_data` /
  `comonoid_from_data` ergonomics in the cofree-comonoid layer.
- **`parallel(::Comonoid, ::Comonoid; validate=false)`** opt-out
  keyword — skips the post-construction `validate_comonoid` call. Watch-list
  item from extensions v2 progress notes; useful in hot paths where
  redundant validation is wasteful.
- **n-ary `parallel(c1, c2, c3, more...)` for Comonoid** — left-folds
  binary parallel; uses `validate=false` for intermediates and
  validates only the final result.

### Changed

- **`free_category_comonoid` deprecated.** Now emits `Base.depwarn`
  forwarding to `free_labeled_transition_comonoid`. The shim handles
  the edge-tuple shape change (`(src, tgt, label)` → `(src, label, tgt)`)
  and keyword translation (`max_depth` → `max_path_length`). To be
  removed in v0.4.
- **`bicomodule_from_data` docstring expanded** with explicit
  coverage requirement on `right_back_directions` (and
  `left_back_directions`): for every `(x, a, e)`-triple over the
  right-coaction codomain, the dictionary must contain a key. The
  failure mode (`KeyError` at coaction-application time) and how to
  attribute it via `validate_bicomodule_*_detailed` are documented.
- **`Project.toml` version** bumped from `0.2.0` to `0.3.1` (the
  `0.3.0` ship was tagged separately but the manifest never picked up
  the bump; this corrects that drift).

### Migration from v0.3.0

- `free_category_comonoid([:A, :B], [(:A, :B, :step)]; max_depth=3)`
  → `free_labeled_transition_comonoid([:A, :B], [(:A, :step, :B)]; max_path_length=3)`.
  The old form keeps working with a depwarn through v0.3.x; remove in v0.4.
- `compose(M, N)` for bicomodules with carrier direction-sets of
  cardinality > 1: position-set count changes from
  `|M.carrier[x]| × #compatible_y` to the correct `Π_a #compatible_y(a)`.
  Downstream code that pattern-matches on the old count needs updating.
- `compose(regular_bicomodule(c), regular_bicomodule(c))` for `c =
  state_system_comonoid({s1, s2})` now produces 2 positions (was 4 in
  v0.3.0). The result still validates and is the unit for composition
  over `c`.

## [0.2.0] — Extensions v1

Driven by an external review of v0.1.0 (Sprint 8) usage on a non-trivial
application. Eight numbered items from the design doc shipped, with one
follow-up item explicitly deferred to a v1.1 PR. Design doc:
`docs/dev/extensions_v1_design.md`.

### Added

- **`AbstractPolynomial`** supertype, with `ConcretePolynomial` reseated
  underneath and the public name `Polynomial` preserved via const alias.
  Existing user code keeps working unchanged.
- **`LazySubst`** polynomial that defers `subst(p, q)` enumeration. Use
  `subst_lazy(p, q)` to construct, `materialize` to force the eager form.
  Composes lazily with itself.
- **`is_subst_of(target, p, q; force_enumerate=false)`** — shape-only
  equality predicate. Cardinality-fast-fail + sample verification, no
  enumeration in the common path. Used by `Bicomodule`, `RightComodule`,
  `LeftComodule`, and `Comonoid` constructors in place of the previous
  `==`-against-`subst(...)` check that was the v0.1.0 bottleneck.
- **`coproduct(ps::Polynomial...)`** — n-ary disjoint union with flat
  `(k, x)` tags. Avoids the nested left-associated tag chain produced
  by repeated binary `+`.
- **`flatten_coproduct(p)`** — best-effort re-tag of left-associated `+`
  chains into the flat form. Documented limitation: positions whose
  natural encoding happens to be `(Int, _)` may mis-classify; prefer
  constructing via `coproduct` from the start.
- **`ValidationResult`**, **`ValidationFailure`**, **`minimal_failing_triple`**
  with structural failure detail (per-failure `law`, `location`,
  `structural_hint`, `actual`, `expected`). Each `validate_*` returns
  `Bool` for back-compat with `Test.jl`'s `@test`; a `validate_*_detailed`
  companion returns the structured `ValidationResult`. Six validators
  refactored: comonoid (lens + category modes), retrofunctor, right /
  left comodule, bicomodule (with `verbose=:all` collecting every
  failing compatibility triple).
- **`Coalgebra`** as a peer type to `Comonoid` and `Bicomodule`, with
  shape-only `validate_coalgebra`. **`CoalgebraMorphism`** with
  commuting-square `validate_coalgebra_morphism`. Convenience
  `moore_machine_coalgebra` constructor and `to_lens` accessor. Existing
  `state_system`, `dynamical_system`, `moore_machine` continue to return
  `Lens` for back-compat.
- **Comonoid arithmetic**: `+` (coproduct of categories), `*` (categorical
  product), `⊗` (Dirichlet/parallel — coincides with `*` for small
  categories; both names exposed for symmetry with `Polynomial`).
- **Bicomodule arithmetic**: `+` (sum over common bases), `⊗` (parallel
  product over tensored bases via polynomial-level carrier tensor),
  `compose` (with Unicode `⊙` infix alias) implementing Niu/Spivak Ch. 8
  prafunctor composition.
- **`subst_targeted_lens(dom, p, q, on_pos, on_dir)`** and
  **`subst_targeted_coaction(carrier, base, on_pos, on_dir; side=...)`**
  — convenience constructors for lenses targeting `subst(p, q)` that
  unpack the `(i, j̄)` and `(a, b)` tuple structure for the user.
- **Symbolic↔concrete interop**: arithmetic operators (`+`, `*`,
  `parallel`, `subst`) auto-promote concrete to symbolic when mixed.
  Equality stays explicit on purpose. Intent-revealing aliases
  `to_symbolic` / `to_concrete` for `lift` / `evaluate`. New tour
  `docs/literate/08_interop.jl`.
- **`set_tabulate_cap!(n)`** wrapper around the cap mutation, returning
  the previous value. Over-cap error message now lists the four escape
  hatches explicitly.

### Changed

- `validate_*` functions return `ValidationResult` via a `_detailed`
  companion; the original `validate_*` names keep returning `Bool` for
  back-compat with `@test`. (The original Q6 design called for soft
  Bool conversion; that approach broke `@test`'s `isa Bool` check, so
  the implementation switched to an explicit `_detailed` companion. See
  design doc §6.1 for the rationale.)
- `verbose` parameter on validators accepts `Bool` or `Symbol` (with
  `:all` collecting every failure rather than stopping at the first).

### Deferred to v1.1

- **Full coequalizer for `compose(::Bicomodule, ::Bicomodule)`.** The
  current implementation is correct for regular bicomodules and
  non-pathological cases but overcounts in the general case. Closing it
  requires nailing down Niu/Spivak Definition 8.31's exact equivalence
  rule — focused work that warrants its own PR with the book at hand.
- **Widen `Lens.dom` and `Lens.cod` to `AbstractPolynomial`.** Would let
  `subst_targeted_lens` return a lens with a `LazySubst` cod (avoiding
  the eager `subst()` materialization). Requires a careful audit of
  every method touching lens dom/cod — composition, equality, validation,
  the Sprint 6 dynamical-system code, Closure (Sprint 5). Deferred to a
  standalone PR with comprehensive regression testing.
- **PR #9 examples** (`bicomodule_walk`, `retrofunctor_categories`,
  `cofree_in_anger`). Existing examples cover Sprint 1–8 basics; the
  v0.2.0 docstrings carry the new APIs. Deferred per maintainer's call.

### Internal

- New file `src/Validation.jl` housing the validation result types.
- Include order: Validation.jl is included before Dynamical.jl
  (Coalgebra references `ValidationFailure`).
- Multiple-dispatch helpers `_struct_equal` / `_struct_hash` replace the
  earlier `isa`-branching helpers for lazy-polynomial bookkeeping.

## [0.1.0] — Initial release

Sprints 1–8 (Niu/Spivak Chapters 1–8): polynomials, lenses, monoidal
products, dynamical systems, comonoids ↔ small categories, cofree
comonoid, comodules + bicomodules. See `docs/dev/historical-design.md`
for the original Sprint 1 design plan and `RELEASE.md` for the v0.1.0
release checklist.
