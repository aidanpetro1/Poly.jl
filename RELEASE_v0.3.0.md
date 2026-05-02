# Poly.jl v0.3.0 — release notes

Commit: `50d6b00` ("Extensions v2: ship v0.3.0 contents") on `main`.

## Retag the existing v0.3.0 (Windows)

The pre-Tier-2-5 state was tagged `v0.3.0` earlier; this release moves that tag
to the head of `main` so it actually points at the v0.3.0 deliverable.

```powershell
git tag -d v0.3.0
git tag -a v0.3.0 -m "Poly.jl v0.3.0 — Extensions v2 (15-item round, 28 Qs resolved 2026-05-01)"
git push origin :refs/tags/v0.3.0
git push origin v0.3.0
git push origin main
```

## What landed in v0.3.0

15-item Extensions v2 round closing the categorical gaps surfaced by
downstream PolyCDS work. Phasing per `docs/dev/extensions_v2_design.md` §16.

### Tier 0 — mechanical
- **#7** `minimal_failing_triple` worked-example docstring
- **#9** `validate_bicomodule_detailed` 5-axiom table in docstring
- **#10** Cofree depth-table in `src/Cofree.jl` header (numerically verified
  against `_trees_at_depth`)
- **#12** `representable(::AbstractVector)` and `(::AbstractSet)` overloads
- **#14** `free_category_comonoid(vertices, edges; max_depth)` with
  multi-arity edge dispatch and depth-bounded handling of cycles
- **#15** `@poly` macro section in `docs/src/quickstart.md`

### Tier 1
- **#1** `parallel(::Comonoid, ::Comonoid)` carrier-tensor with Q1.2
  validate-at-construction.
  - Q1.1 became a hard break (originally soft): `⊗` and `parallel` share
    a function via `const var"⊗" = parallel` in `Monoidal.jl`, so they
    cannot disagree by signature. v0.3 collapses them for `Comonoid`
    arguments. Migration: `c ⊗ d` (categorical product) → `c * d`.

### Tier 2
- **#2** `BicomoduleMorphism` first-class 2-cells in Cat#. Vertical and
  horizontal composition, whiskering, `validate_bicomodule_morphism[_detailed]`
  matching `validate_bicomodule_detailed`'s `ValidationFailure` shape.
- **#5** `bicomodule_from_data` + `comonoid_from_data` authoring helpers.
  Validates by default; `validate=false` for intermediate constructions.
- **#6** `back_directions(L::Lens)` + `BackDirectionTable` (Dict-like wrapper
  with multi-line `show`). `sharp_L` / `sharp_R` shorthands. Cap-aware:
  `materialize=:auto` returns callable above `TABULATE_SIZE_CAP`,
  `materialize=true` errors with the cap message.

### Tier 3
- **#3** Kan extensions: `kan_along_bicomodule(D, M; direction)` for
  finite cases + `kan_2cat(D, F; direction)` for symbolic-aware. Both
  return a `KanExtension` record with `extension`, `unit::BicomoduleMorphism`,
  `direction`, plus `factor_through(k, α)` for the universal property.
  - Identity-D case ships in v0.3; non-identity errors with v0.3.x
    pointer (requires symbolic-layer coequalizer).
  - Σ_D / Π_D unicode aliases.
  - Companion design note at `docs/dev/kan_extensions_construction.md`.

### Tier 4
- **#4** `PolyElement(p, position, assignment)` wrapper + `support(::PolyElement)`
  computing Fairbanks-style support (image-of-assignment for polynomial
  functors). Pair-of-args forwarder. Symbolic side: `free_variables(::SymExpr)`
  walking `SymVar`/`SymLit`/`SymOp` recursively.

### Tier 5
- **#8** `LazyCofreeComonoid` deferring tower-of-exponentials enumeration.
  Cached materialization, `tree_at(c, i)`, `clear_cache!`, lazy
  `validate_comonoid` (returns true via Niu/Spivak Thm 8.45 without
  materializing; `force=true` runs the full validator).
- **#11** `docs/src/tours/08_bicomodule_walkthrough.md` — Ch. 8 worked
  example using a 2-state state-system bicomodule. Walks through carrier
  selection, position-map / back-direction tables, `bicomodule_from_data`,
  `validate_bicomodule_detailed` debugging via `minimal_failing_triple`,
  `sharp_L` / `sharp_R` inspection, comodule-over-bicomodule structure.

### Deferred
- **#13** Cofree-on-a-comonoid → Extensions v3 (per Q13.1).

## Tests

324/324 v2 assertions across 9 new test files:

```
test_extensions_v2_representable.jl       — 6 testsets, 15 assertions
test_extensions_v2_free_category.jl       — 22 testsets, 52 assertions
test_extensions_v2_parallel_comonoid.jl   — 19 testsets, 41 assertions
test_extensions_v2_back_directions.jl     — 19 testsets, 44 assertions
test_extensions_v2_from_data.jl           —  9 testsets, 18 assertions
test_extensions_v2_bicomodule_morphism.jl — 16 testsets, 38 assertions
test_extensions_v2_kan.jl                 — 16 testsets, 30 assertions
test_extensions_v2_support.jl             — 16 testsets, 35 assertions
test_extensions_v2_lazy_cofree.jl         — 22 testsets, 51 assertions
```

Each file includes a dedicated "Adversarial tests" section beyond the
happy-path coverage. Total suite: 850+ tests across Sprint 1–8 +
Extensions v1 + v2.

Run:

```sh
julia --project=. -e 'using Pkg; Pkg.test()'
```

## API stability

v0.3 is the first release with a non-trivial migration burden:

- `c ⊗ d` for two `Comonoid`s now means the carrier-tensor (`parallel`),
  not the categorical product. Use `c * d` for the categorical product.
- The `_comonoid_carrier_tensor` internal name is now an alias for
  `parallel` in `src/Cofree.jl`. Drop in v0.4.

All other v0.2 surface continues to work.
