# Handoff — Lazy `Lens.cod` (`AbstractPolynomial` widening)

## TL;DR

`Lens.cod` was hard-typed `::Polynomial` (concrete), which forced every coaction or duplicator with a substitution-polynomial codomain to enumerate `Σ_i |q|^|p[i]|` positions. For PolyCDS v1.1's joint bicomodules (carriers ~20 positions × 20 directions each) this is ~10²⁶ positions — uncon­structable.

This change widens `Lens.cod` to `::AbstractPolynomial` and routes the three Bicomodule-⊗ codomains through `subst_lazy` instead of eager `subst`. Joint bicomodules now build in finite memory and validate in time linear in the carrier/base sizes.

## Files changed

| File | Change |
|------|--------|
| `src/Lens.jl` | Widened `cod::Polynomial` → `cod::AbstractPolynomial` on the struct + both constructor signatures. Switched `compose` and `==` cod-checks to `_struct_equal`. Materialize-on-demand in `(f::Lens)(X)`. **In `compose`**, swapped `r.positions` → `positions(r)` so a lazy `g.cod` flows through the accessor instead of the missing field. |
| `src/Monoidal.jl` | Cross-type `==(::LazySubst, ::ConcretePolynomial)` (+ inverse) and matching `_struct_equal` methods. Cross-type `==(::SubstPolySet, ::FinPolySet)` (+ inverse) so a `Lens` with a lazy cod compares equal to a structurally-identical eager-cod lens (without this, `PolyFunction.==` on `on_positions` returned false at the lazy-vs-eager boundary). Fallback methods for `+`, `*`, `parallel`, `subst`, `coproduct` on `AbstractPolynomial` that materialize-and-delegate. |
| `src/Cofree.jl` | Three `subst(...)` → `subst_lazy(...)` swaps: `_comonoid_carrier_tensor` joint duplicator, `parallel(::Bicomodule,…)` joint left + right coactions. Also: `cofree_universal` materializes `labeling.cod` defensively so its `.positions`-field path stays valid for lazy callers. |
| `src/Comonoid.jl` | Four `subst(carrier, carrier)` → `subst_lazy(carrier, carrier)` swaps: `from_category`, `state_system_comonoid`, `discrete_comonoid`, `monoid_comonoid`. The categorical-bridge `Comonoid +`/`*`/`⊗` inherit the fix. |
| `src/Symbolic.jl` | `lift(::AbstractPolynomial)` fallback (materializes). `to_latex(::LazySubst)` direct rendering as `(p ◁ q)`. |
| `test/test_extensions_lazy_lens_cod.jl` | New file; 6 testsets. |
| `test/runtests.jl` | Wires the new test file into the suite. |

## What got widened, what didn't

- **Widened**: `Lens.cod`. Now accepts any `AbstractPolynomial`, including `LazySubst`.
- **Not widened**: `Lens.dom` — kept `::Polynomial` (concrete). The dom is iterated over directly by every Lens consumer (`compose`, `==`, validation, retrofunctor laws). Widening it would force materialization at every consumer; not worth the churn.

## Backward compat

- `==(lens.cod, subst(p, q))` style asserts still pass: cross-type `==(::LazySubst, ::ConcretePolynomial)` materializes the lazy side and structurally compares. This pays the eager enumeration cost the original code would have, but only when the comparison is explicitly invoked — Bicomodule construction stays on the cheap `is_subst_of` path.
- All existing tests should pass unchanged.
- `cs.duplicator.cod isa Polynomial` — was `true`, is now `false` (it's `LazySubst`). Downstream code that pattern-matched on the concrete type needs to widen to `AbstractPolynomial` or call `materialize` first.

## New regression test (PolyCDS v1.1 mirror)

`test/test_extensions_lazy_lens_cod.jl` builds two `state_system_comonoid`s of sizes 4 and 5, makes them into regular bicomodules, takes the parallel product, and validates. The joint carrier has 20 positions × 20 directions each — `subst(carrier, carrier)` eagerly would have 20·20²⁰ ≈ 10²⁶ positions. The test asserts:

1. The duplicator's cod and the joint coactions' cods are `LazySubst`.
2. `Bicomodule(...)` accepts the lazy-cod coactions.
3. `validate_bicomodule_detailed` passes.

If this test ever times out or OOMs, something has reverted to eager construction.

## Hashes & gotchas

- The hash invariant for cross-type `==(::LazySubst, ::ConcretePolynomial)` is technically violated (the two tag their hashes differently). In practice this never matters because cods don't end up as Dict/Set keys, but if you ever do put them in a Dict, normalize to one form first.
- The `_struct_equal` fallback for two `AbstractPolynomial` values that don't match a more-specific method is identity (`===`). If a future lazy variant is added (say `LazyParallel`), it needs its own `_struct_equal` methods, including cross-type with `ConcretePolynomial`.
- `subst(::AbstractPolynomial, ::AbstractPolynomial)` materializes both operands. For lazy chaining, use `subst_lazy` directly — that's the path that stays lazy.

## Suggested follow-ups (not done in this pass)

- **`Lens.dom` widening** — only worth it if a use case appears for lenses *out of* a lazy polynomial. Not needed for PolyCDS v1.1.
- **Composition across the lazy/concrete boundary** — `compose(f, g)` with `f.cod::LazySubst` and `g.dom::ConcretePolynomial` will materialize `f.cod` on the equality check. If this ends up on a hot path, replace with `is_subst_of`-style structural matching.
- **Hash consistency** — if cods enter Dicts, define cross-type `hash` so structurally-equal lazy/concrete pairs hash the same. Currently they don't.
