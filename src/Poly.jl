"""
    Poly

A Julia library for polynomial functors `p : Set → Set`, dependent lenses,
and the categorical structures built on top of them, following Niu and Spivak's
*Polynomial Functors: A Mathematical Theory of Interaction* (2024).

This file is the module entry point; the implementation is split across:

  - `Cardinality.jl`     — the cardinality algebra (`Finite`, `ℵ₀`, `𝔠`, symbolic).
  - `PolySets.jl`        — the `PolySet` hierarchy (mixed finite + symbolic).
  - `PolyFunctions.jl`   — `PolyFunction` (lazy + tabulate) and `DependentFunction`.
  - `Polynomial.jl`      — `Polynomial`, special classes, `apply`,
                           `cardinality_of_apply`, `is_iso(_strict)`, displays,
                           and the corolla-forest renderer.
  - `Lens.jl`            — `Lens`, identity, vertical composition, equality,
                           polybox renderer, `lens_count`.
  - `Monoidal.jl`        — concrete `+`, `×`, `⊗`, `▷` for Polynomial and Lens.
  - `Closure.jl`         — closure `[q, r]` of `⊗`, sections `Γ(p)`,
                           do-nothing section, eval_lens, derivative.
  - `Dynamical.jl`       — Moore machines and dependent dynamical systems
                           as `Sy^S → p` lenses; step / trajectory helpers.
  - `Comonoid.jl`        — comonoids in `(Poly, y, ▷)` and the
                           Ahman–Uustalu correspondence with small categories;
                           retrofunctors.
  - `Cofree.jl`          — depth-bounded cofree comonoid `T_p`, behavior
                           trees, and right comodules.
  - `Macros.jl`          — `@poly` for terse polynomial construction.
  - `Symbolic.jl`        — parallel symbolic layer (`SymbolicPolynomial`,
                           `SymbolicLens`, expression trees, `simplify`,
                           `lift`, `evaluate`, `sym_equal`).
  - `Demos.jl`           — human-readable acceptance demos.

The `test/runtests.jl` suite covers everything programmatically.
"""
module Poly

import Base: +, *, ^, ==, show, length, iterate, in, eltype, isequal, hash

export
    # Cardinality
    Cardinality, Finite, CountablyInfinite, Continuum, SymbolicCardinality,
    CardinalityExpr, isfinite_card,

    # PolySet
    PolySet, FinPolySet, NatSet, IntSet, RealSet, IntervalSet,
    ProductSet, SumSet, ExpSet, SymbolicSet, cardinality,

    # PolyFunction / DependentFunction
    PolyFunction, tabulate, untabulate, identity_polyfunction,
    TABULATE_SIZE_CAP, set_tabulate_cap!,
    DependentFunction, indexed_family,

    # Polynomial
    AbstractPolynomial, ConcretePolynomial, Polynomial, positions, direction_at,
    y, zero_poly, one_poly,
    constant, linear, monomial, representable,
    is_constant, is_linear, is_monomial, is_representable,
    is_iso, is_iso_strict,
    # Element handle + support (Extensions v2 PR #4).
    PolyElement, support,
    apply, cardinality_of_apply, corolla_forest,

    # Lens
    Lens, identity_lens, compose, lens_count, polybox,
    # Lens back-direction inspection (Extensions v2 PR #6).
    BackDirectionTable, back_directions,

    # Monoidal products (Sprint 3)
    var"×", var"⊗",

    # Composition product (Sprint 4). Book convention is `◁` but Julia's
    # parser doesn't recognize it; we use `▷` as the infix alias. The named
    # form is `subst` (Niu/Spivak's "substitution product"). See
    # `Monoidal.jl` for the rationale.
    var"▷", subst, subst_n,

    # Lazy composition product (Extensions v1, PR #1). Use `subst_lazy` when
    # building bicomodules or chaining substitutions to defer the
    # `Σ_i |q|^|p[i]|` enumeration until truly needed; call `materialize` to
    # force the eager `Polynomial` form. `is_subst_of` checks shape equality
    # without enumeration — used by `Bicomodule`'s constructor.
    LazySubst, subst_lazy, materialize, is_subst_of,

    # Convenience constructors for lenses targeting subst(p, q) (PR #5).
    # `subst_targeted_lens` accepts the natural-shape position and direction
    # callbacks; `subst_targeted_coaction` pre-fills the (p, q) operands
    # based on which side of a bicomodule the coaction lives on.
    subst_targeted_lens, subst_targeted_coaction,

    # n-ary flat coproduct (Extensions v1, PR #3). `coproduct(p1, ..., pn)`
    # produces flat `(k, x)` tags rather than the nested left-associated
    # form of `p1 + p2 + ... + pn`. `flatten_coproduct` re-tags an existing
    # binary-`+` chain into the flat form (with structural-detection caveats).
    coproduct, flatten_coproduct,

    # Closure of ⊗, sections, derivative (Sprint 5)
    internal_hom, sections, section_lens, do_nothing_section,
    eval_lens, derivative,

    # Dynamical systems (Sprint 6). Note: `step` is a method extension of
    # `Base.step` rather than a freshly-exported name, so it's not in this
    # list — `using Poly` is enough; `step(φ, s, d)` dispatches via Base.
    state_system, is_state_system, moore_machine, dynamical_system,
    initial_state, trajectory, output_trajectory,
    state_output_trajectory, juxtapose, wrap,

    # First-class Coalgebra (Extensions v1, PR #4). Peer type to Comonoid /
    # Bicomodule for coalgebras of an *endofunctor* (no laws beyond shape;
    # comodules are different beasts, see RightComodule etc.). Existing
    # `state_system`, `dynamical_system`, `moore_machine` keep returning
    # `Lens` — wrap in `Coalgebra(::Lens)` for the typed object.
    Coalgebra, CoalgebraMorphism, to_lens,
    moore_machine_coalgebra,
    validate_coalgebra, validate_coalgebra_detailed,
    validate_coalgebra_morphism, validate_coalgebra_morphism_detailed,

    # Comonoids = categories (Sprint 7)
    Comonoid, SmallCategory, Retrofunctor,
    to_category, from_category,
    validate_category_laws, validate_comonoid,
    validate_retrofunctor,
    state_system_comonoid, discrete_comonoid, monoid_comonoid,
    identity_retrofunctor,
    # Free category on a graph (Extensions v2, PR #14).
    # `free_category_comonoid` deprecated in v0.3.1 (depwarn forwarder
    # to `free_labeled_transition_comonoid`); removed in v0.4.
    free_category_comonoid, free_labeled_transition_comonoid,
    # Authoring helper (Extensions v2 PR #5).
    comonoid_from_data,

    # Validation results (Extensions v1, PR #6). Public `validate_*` return
    # `Bool` for back-compat with `@test` and existing call sites. Each has
    # a `validate_*_detailed` companion returning the structured
    # `ValidationResult` with per-failure detail (`law`, `location`,
    # `structural_hint`, `actual`, `expected`).
    ValidationResult, ValidationFailure, minimal_failing_triple,
    validate_category_laws_detailed, validate_comonoid_detailed,
    validate_retrofunctor_detailed,

    # Cofree comonoid + comodules + bicomodules (Sprint 8)
    BehaviorTree, behavior_trees, tree_paths, tree_walk,
    # Path-dict builder for BehaviorTree (v0.3.x).
    behavior_tree_from_paths,
    cofree_comonoid, cofree_unit, cofree_universal,
    RightComodule, regular_right_comodule,
    validate_right_comodule, validate_right_comodule_detailed,
    LeftComodule, regular_left_comodule,
    validate_left_comodule, validate_left_comodule_detailed,
    Bicomodule, regular_bicomodule,
    validate_bicomodule, validate_bicomodule_detailed,
    # Composition pre-flight (v0.3.x). Use before `compose(M, N)` when
    # you want attributed failure information (M-side / N-side / cross).
    validate_bicomodule_composition, validate_bicomodule_composition_detailed,
    # Lazy bicomodule composite carrier (v0.3.x — full Niu/Spivak
    # coequalizer, eager+lazy paths). `compose_lazy` is the lazy variant
    # of `compose`; `LazyBicomoduleCarrier` is the underlying polynomial.
    compose_lazy, LazyBicomoduleCarrier,
    # Authoring helper (Extensions v2 PR #5).
    bicomodule_from_data,
    # Bicomodule-specific back-direction shorthands (Extensions v2 PR #6).
    sharp_L, sharp_R,
    # Bicomodule 2-cells (Extensions v2 PR #2).
    BicomoduleMorphism, identity_bicomodule_morphism,
    validate_bicomodule_morphism, validate_bicomodule_morphism_detailed,
    whisker_left, whisker_right, horizontal_compose,
    # Kan extensions of bicomodules (Extensions v2 PR #3).
    KanExtension, kan_along_bicomodule, kan_2cat, factor_through,
    var"Σ_D", var"Π_D",
    # Lazy cofree comonoid (Extensions v2 PR #8).
    LazyCofreeComonoid, cofree_lazy, clear_cache!, tree_at, is_materialized,
    eraser, duplicator,

    # Bicomodule composition (Extensions v1, PR #2). The Unicode `⊙`
    # alias gives book-style infix; `compose` is the named form. The
    # Comonoid-arithmetic operators `+`, `*`, `⊗` lift through `Base`'s
    # operator infrastructure, no fresh exports needed beyond what
    # already gets re-exported via `import Base: +, *`.
    var"⊙",

    # Macros
    @poly,

    # Symbolic layer. Note: AST node types (`SymExpr`, `SymVar`, `SymLit`,
    # `SymOp`) are intentionally NOT exported — users build symbolic
    # polynomials via `sympoly`, `symlens`, `lift`, and the operators.
    # Reach into `Poly.SymExpr` etc. only if you need to write custom rules.
    SymbolicPolynomial, SymbolicLens,
    sym_y, sym_zero, sym_one, sympoly, symlens, sym_id,
    parallel,
    lift, evaluate, simplify, sym_equal,
    # Intent-revealing aliases (Extensions v1, PR #8) — same semantics as
    # `lift` / `evaluate`, names spelled out for boundary-crossing calls.
    to_symbolic, to_concrete,
    Rule, rules,
    # Symbolic-side support: free-variable extraction (Extensions v2 PR #4).
    free_variables,
    to_latex, latex_display


include("Cardinality.jl")
include("PolySets.jl")
include("PolyFunctions.jl")
include("Polynomial.jl")
include("Lens.jl")
include("Monoidal.jl")
include("Closure.jl")
# Validation types — referenced by Dynamical.jl (Coalgebra) and the
# comonoid/comodule validators. Must precede everything that uses
# `ValidationResult`, `ValidationFailure`, etc.
include("Validation.jl")
include("Dynamical.jl")
include("Comonoid.jl")
include("Cofree.jl")
include("Macros.jl")
include("Symbolic.jl")
include("Demos.jl")

end # module Poly
