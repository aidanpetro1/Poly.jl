# Kan extensions of bicomodules — companion design note for Extensions v2 #3

> **Status**: design note, written 2026-05-01 to ground the implementation
> of `kan_along_bicomodule` and `kan_2cat`. Per the v2 design doc §3.3,
> #3 ships in v0.3.0 with both flavors. This note pins down what the
> functions return and where the math is delicate; the implementation
> follows.

## 1. Two flavors

Per Q3.1 (resolved 2026-05-01), v0.3 ships **both** Kan-extension
constructions. They differ in what they extend and over what.

### 1a. `kan_along_bicomodule(D::Bicomodule, M::AbstractComodule; direction)`

**Setting.** `D : C ↛ E` is a bicomodule between comonoids `C` and `E`
(equivalently, a prafunctor `C → E` per Niu/Spivak Theorem 8.100). `M` is
a one-sided comodule of `C` (left or right) — equivalently, a copresheaf
or discrete-opfibration-like structure on `C` (Prop 8.88).

**Output.** A comodule of `E` obtained by extending `M` along the
prafunctor `D`.

  - `direction = :left` produces `Σ_D M`, the **left Kan extension** —
    "push M through D's outputs."
  - `direction = :right` produces `Π_D M`, the **right Kan extension** —
    dual; "pull M back along D" with universal *cone* property.

**Computability.** Per Q3.2 resolution, this flavor is **finite-only**
in v0.3. Both `D`'s carriers and `M`'s carrier must have finite
position-sets and finite direction-sets so the underlying (co)limit
construction terminates without invoking the symbolic layer.

### 1b. `kan_2cat(D::Bicomodule, F::Bicomodule; direction)`

**Setting.** Both `D` and `F` are bicomodules viewed as 1-cells in the
2-category obtained from Cat# by collapsing 2-cells. `D : C ↛ E` and
`F : C ↛ E'` (so they share the same source comonoid `C`).

**Output.** A bicomodule `Lan_D F : E ↛ E'` (left Kan) or
`Ran_D F : E ↛ E'` (right Kan) extending `F` along `D` in the
2-categorical sense.

**Computability.** Per Q3.2 resolution, this flavor is **symbolic-aware**.
Inputs may be `LazySubst` or have symbolic-set positions; the
construction uses the Symbolic.jl layer to express the underlying
(co)limit. Materialization is on-demand.

## 2. The `KanExtension` record

Per Q3.3 resolution (richest option), Kan-extension functions return a
`KanExtension` record carrying:

  - `extension :: T` — the comodule (3a) or bicomodule (3b) the
    construction produces.
  - `unit :: BicomoduleMorphism` — the canonical 2-cell witnessing the
    universal property. For left Kan, this is the unit `η : M ⇒ D ⊙ Σ_D M`
    (3a) or `η : F ⇒ D ⊙ Lan_D F` (3b). For right Kan, it's the counit
    `ε`. Direction is recorded so consumers can interpret correctly.
  - `direction :: Symbol` — `:left` or `:right`.
  - Internal data needed by `factor_through`.

```julia
struct KanExtension{T}
    extension::T
    unit::BicomoduleMorphism      # unit (η) for left Kan; counit (ε) for right Kan
    direction::Symbol             # :left or :right
    # Internal data:
    source::Bicomodule            # D — the bicomodule we extended along
    input::Any                    # the M (or F) that was extended
end
```

The `factor_through` method exhibits the universal property: given any
2-cell that "should factor through the unit," it returns the unique
factoring morphism.

```julia
"""
    factor_through(k::KanExtension, α::BicomoduleMorphism) -> BicomoduleMorphism

Given a 2-cell α : input ⇒ (D ⊙ N) for some bicomodule N appropriate to
the Kan setting, return the unique 2-cell `Σ_D input ⇒ N` whose
post-composition with `k.unit` recovers α.

For right Kan, the direction reverses: α : (D ⊙ N) ⇒ input gives a
unique N ⇒ Π_D input.

Errors if α's shape doesn't match the Kan setting (source, target, base
comonoids).
"""
factor_through(k::KanExtension, α::BicomoduleMorphism) :: BicomoduleMorphism
```

## 3. Niu/Spivak Ch. 8 anchors

  - **Theorem 8.100**: bicomodules ≃ prafunctors. This justifies treating
    `D` in 3a as a prafunctor `C → E` and computing Kan extensions of
    presheaf-like comodules along it.
  - **Prop 8.88**: left C-comodules ≃ copresheaves on `C`. So `Σ_D M` for
    M a left comodule lifts to a copresheaf-extension construction.
  - **Prop 8.94**: free right C-comodule on a set G is `y^G ⊗ 𝔠`. The
    explicit form gives a baseline for testing — Kan extensions of free
    comodules should match a direct calculation.
  - **§8.2 colimits**: `Cat#` has all small colimits (Cor 8.72) and
    limits (Cor 8.76), created by the forgetful U. So the (co)limits
    underlying Kan extensions exist abstractly — we just have to
    compute them concretely.

The book does not give a single "Kan-extension formula" we can lift
verbatim, but the pieces are present:

  - For `kan_along_bicomodule(D, M; direction=:left)` with `M` a right
    `C`-comodule and `D : C ↛ E`: the result is a right `E`-comodule
    obtained by `M ⊙_C D` (bicomodule composition). Universal property:
    any morphism `M ⇒ D ⊙ N` for some right `E`-comodule `N` factors
    uniquely through the unit. Implementation matches our existing
    `compose(::Bicomodule, ::Bicomodule)` plus a wrapper.
  - For `kan_along_bicomodule(D, M; direction=:right)`: dual; involves
    the right adjoint of `D ⊙ −`. Computability is finer; for finite
    inputs it reduces to a section-counting calculation in the spirit
    of `lens_count` / `sections`.
  - For `kan_2cat(D, F; direction=:left)`: in the collapsed 2-category,
    Kan extension reduces to a parameterized bicomodule composition with
    a coequalizer adjustment. The symbolic layer expresses the
    coequalizer when the carriers don't fit in `TABULATE_SIZE_CAP`.

## 4. Implementation phasing

The module ships in this order (within #3):

1. **`KanExtension` struct + factor_through** for the simplest case
   (identity bicomodule), where `Σ_id_C M = M` and the unit is the
   identity 2-cell. Pins the API surface and the universal-property
   round-trip.
2. **`kan_along_bicomodule(D, M; direction=:left)`** for finite right
   C-comodules over D. Builds on top of `compose(::Bicomodule,
   ::Bicomodule)` from PR #2.
3. **`kan_along_bicomodule(D, M; direction=:right)`** for the same
   inputs. May require a separate `right_kan_along_*` helper.
4. **`kan_2cat(D, F; direction=:left/:right)`** for both finite and
   symbolic inputs. Uses the Symbolic.jl layer when inputs are non-finite.
5. **Unicode aliases** `Σ_D`, `Π_D` exported alongside the prose names
   per Q3.4.

Each phase has a corresponding test set:

  - Identity Kan: `kan_along_bicomodule(id_C, M)` returns a
    `KanExtension` whose `extension == M` (up to iso) and whose unit is
    the identity 2-cell.
  - Universal property: for any compatible 2-cell α, `factor_through(k,
    α)` composed back through `k.unit` recovers α.
  - Reviewer-supplied audit/likelihood worked example (one row).

## 5. Open questions for runtime-confirmation

  - **Q3-impl-1**: For `kan_along_bicomodule(D, M; :left)` with `D` a
    non-trivial bicomodule and `M` a right `C`-comodule, does the result
    `M ⊙_C D` automatically inherit the right comodule structure of `E`,
    or is there a coercion step? (Likely yes by the bicomodule-composition
    construction, but worth verifying with a concrete test.)
  - **Q3-impl-2**: How does the right-Kan-extension's universal property
    interact with finite truncation? If any input has empty positions or
    direction-sets, edge-case behavior of `factor_through`?
  - **Q3-impl-3**: For `kan_2cat`, what's the minimum set of operations
    on the symbolic layer needed? Likely `subst_lazy` on
    `SymbolicPolynomial` and a coequalizer placeholder. May depend on
    whether Symbolic.jl already exposes coequalizers (it does not, as of
    v0.3.0 audit).

These are flagged for resolution during implementation rather than
upfront — they'll surface concretely when writing tests against the
universal property.

## 6. Out of scope for v0.3

  - Kan extensions of *bicomodules* (not just comodules) along
    bicomodules in the full double-category sense. The `kan_2cat`
    flavor handles the collapsed-2-category case but not the doubly
    parametric one.
  - Kan extensions in `Cat` (the 1-category of categories), separate
    from `Cat#`. Niu/Spivak focus on `Cat#`; `Cat` Kan extensions are
    standard and handled by Catlab.jl.
