# Poly.jl v0.3.1 — release notes

Concrete Poly v0.3.x asks. Driven by external feedback from PolyCDS /
SOAP-style modeling work on v0.3.0.

## Tag (Windows PowerShell)

```powershell
git add -A
git commit -m "v0.3.1: Concrete Poly v0.3.x asks (full coequalizer compose, Π_D, free_labeled_transition_comonoid, ...)"
git tag -a v0.3.1 -m "Poly.jl v0.3.1 — full Niu/Spivak compose coequalizer + right-Kan + PolyCDS conveniences"
git push origin main
git push origin v0.3.1
```

## What landed in v0.3.1

10 numbered items in priority order, all green on the existing test
suite (3 pre-existing kan tests updated to match the new behavior;
no regressions elsewhere).

### Priority 1 — `compose(::Bicomodule, ::Bicomodule)` full coequalizer

Closes the v1.1 deferral. Carrier now correctly uses the equalizer
construction (positions = `(x, σ)` with `σ : X[x] → Y.positions`
matching D-routing) rather than the regular-bicomodule approximation
that overcounted in the general case.

- `compose(M, N)` — eager enumeration; correct in the full case.
- `compose_lazy(M, N)` — defers enumeration via
  `LazyBicomoduleCarrier <: AbstractPolynomial`. Use when
  `Π_a #compatible_y(a)` would be too large.
- Verified: `compose(regular_bicomodule(c), regular_bicomodule(c))`
  for `c = state_system_comonoid({s1, s2})` now produces 2 positions
  (was 4 in v0.3.0); validates green.

### Priority 2 — `validate_bicomodule_composition[_detailed]`

Pre-flight check for `compose(M, N)`. Failures are attributed to
`:M`, `:N`, or `:cross` (M-side / N-side / cross-coherence between
them). Each failure's `location[1]` carries the bucket; downstream
code can branch on it to know which operand to investigate.

### Priority 3 — Right-Kan extensions (`Π_D`)

Mirrors the left-Kan structure. Identity-D ships fully; finite
non-identity D builds via the dual section construction. `kan_2cat`
finite path delegates to `kan_along_bicomodule` (for finite carriers
the 2-cat-collapsed and bicomodule-along-bicomodule constructions
agree). Symbolic non-identity D rolls into v0.4.

`Π_D` unicode alias and `factor_through` extended to right-direction
Kan extensions.

### Priority 4 — `free_labeled_transition_comonoid`

PolyCDS-aligned canonical builder for `D` and `P_d`. Edge shape
`(src, label, tgt)` (labeled transition system convention); two-tuple
`(src, tgt)` also accepted with auto-label. `max_path_length` keyword
caps cyclic-graph truncation. **Deprecates `free_category_comonoid`**
which is now a depwarn shim forwarding to the new function (handles
edge-tuple swap and keyword translation); removed in v0.4.

### Priority 5 — Polish bundle

- `Project.toml` version bumped from `0.2.0` to `0.3.1`.
- `bicomodule_from_data` docstring expanded with explicit coverage
  requirement on `right_back_directions` / `left_back_directions`.
- `behavior_tree_from_paths(label_at_root, paths)` — convenience
  builder taking a flat path → label dict (mirrors
  `bicomodule_from_data` ergonomics in the cofree-comonoid layer).
- `parallel(::Comonoid, ::Comonoid; validate=false)` opt-out.
- n-ary `parallel(c1, c2, c3, ...)` for Comonoid.

## Tests

All previously-passing test files still green. Three tests in
`test/test_extensions_v2_kan.jl` updated to reflect the new behavior
(right-Kan / Π_D no longer error for identity D).

```sh
julia --project=. -e 'using Pkg; Pkg.test()'
```

## Migration from v0.3.0

- `free_category_comonoid([:A, :B], [(:A, :B, :step)]; max_depth=3)`
  → `free_labeled_transition_comonoid([:A, :B], [(:A, :step, :B)]; max_path_length=3)`.
  Old form keeps working with depwarn through v0.3.x; remove in v0.4.
- `compose(M, N)` for bicomodules with carrier direction-sets of
  cardinality > 1: position-set count changes. Downstream code that
  pattern-matches on the old count needs updating. The new count is
  the correct categorical answer.

## Internal: build-time gotchas

- The `Edit` tool truncates `src/Cofree.jl` at random byte boundaries
  during long sessions, dropping everything past where it touched.
  Mitigation: use `bash` heredocs / `python3` writes for large
  appends, and verify with `tail` and `wc -l` after each modification.
- Julia 1.12 (Windows) is stricter about trailing whitespace at file
  boundaries than 1.10 (sandbox). After non-trivial file edits run
  `python3 -c "data.rstrip() + b'\n'"` over the affected files to
  clean trailing whitespace before saving.
