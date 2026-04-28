# Changelog

All notable changes to Poly.jl. Format follows [Keep a Changelog](https://keepachangelog.com/);
versioning follows [Semantic Versioning](https://semver.org/).

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
