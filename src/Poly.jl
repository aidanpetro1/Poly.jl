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
    PolyFunction, tabulate, untabulate, identity_polyfunction, TABULATE_SIZE_CAP,
    DependentFunction, indexed_family,

    # Polynomial
    Polynomial, positions, direction_at,
    y, zero_poly, one_poly,
    constant, linear, monomial, representable,
    is_constant, is_linear, is_monomial, is_representable,
    is_iso, is_iso_strict,
    apply, cardinality_of_apply, corolla_forest,

    # Lens
    Lens, identity_lens, compose, lens_count, polybox,

    # Monoidal products (Sprint 3)
    var"×", var"⊗",

    # Composition product (Sprint 4). Book convention is `◁` but Julia's
    # parser doesn't recognize it; we use `▷` as the infix alias. The named
    # form is `subst` (Niu/Spivak's "substitution product"). See
    # `Monoidal.jl` for the rationale.
    var"▷", subst, subst_n,

    # Closure of ⊗, sections, derivative (Sprint 5)
    internal_hom, sections, section_lens, do_nothing_section,
    eval_lens, derivative,

    # Dynamical systems (Sprint 6). Note: `step` is a method extension of
    # `Base.step` rather than a freshly-exported name, so it's not in this
    # list — `using Poly` is enough; `step(φ, s, d)` dispatches via Base.
    state_system, is_state_system, moore_machine, dynamical_system,
    initial_state, trajectory, output_trajectory,
    state_output_trajectory, juxtapose, wrap,

    # Comonoids = categories (Sprint 7)
    Comonoid, SmallCategory, Retrofunctor,
    to_category, from_category,
    validate_category_laws, validate_comonoid,
    validate_retrofunctor,
    state_system_comonoid, discrete_comonoid, monoid_comonoid,
    identity_retrofunctor,

    # Cofree comonoid + comodules + bicomodules (Sprint 8)
    BehaviorTree, behavior_trees, tree_paths, tree_walk,
    cofree_comonoid, cofree_unit, cofree_universal,
    RightComodule, regular_right_comodule, validate_right_comodule,
    LeftComodule, regular_left_comodule, validate_left_comodule,
    Bicomodule, regular_bicomodule, validate_bicomodule,

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
    Rule, rules,
    to_latex, latex_display

include("Cardinality.jl")
include("PolySets.jl")
include("PolyFunctions.jl")
include("Polynomial.jl")
include("Lens.jl")
include("Monoidal.jl")
include("Closure.jl")
include("Dynamical.jl")
include("Comonoid.jl")
include("Cofree.jl")
include("Macros.jl")
include("Symbolic.jl")
include("Demos.jl")

end # module Poly
