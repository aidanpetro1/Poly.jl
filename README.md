# Poly.jl

[![CI](https://github.com/aidanpetro1/Poly.jl/actions/workflows/CI.yml/badge.svg)](https://github.com/aidanpetro1/Poly.jl/actions/workflows/CI.yml)
[![Docs](https://img.shields.io/badge/docs-stable-blue.svg)](https://aidanpetro1.github.io/Poly.jl/stable/)
[![License: MIT](https://img.shields.io/badge/license-MIT-yellow.svg)](LICENSE)

A Julia library for **polynomial functors** in the categorical sense — `p : Set → Set` of the form `p ≅ Σ_{i ∈ p(1)} y^{p[i]}` — and the categorical machinery built on them: dependent lenses, the four monoidal products, dynamical systems, the Ahman–Uustalu correspondence between comonoids in `(Poly, y, ◁)` and small categories, the cofree comonoid `T_p`, and bicomodules.

This library follows Niu and Spivak's *Polynomial Functors: A Mathematical Theory of Interaction* (2024). It is **not** a polynomial-arithmetic library — there are no rings, no GCDs. The objects here model interaction.

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
| Ext v2 (v0.3) | `parallel(::Comonoid, ::Comonoid)` carrier-tensor, `BicomoduleMorphism` 2-cells with horizontal composition, Kan extensions (`kan_along_bicomodule` + `kan_2cat` + `KanExtension` record), `support` / `PolyElement` / `free_variables` (Fairbanks Set-sets), `bicomodule_from_data` + `comonoid_from_data`, `back_directions` / `BackDirectionTable` / `sharp_L` / `sharp_R`, `LazyCofreeComonoid`, `free_category_comonoid`, axiom listings + cofree depth-table docs | 3–8 |

Plus a parallel symbolic layer (`SymbolicPolynomial`, `SymbolicLens`, ~25 rewrite rules with trace mode), a `@poly` macro, and a LaTeX renderer. Chapter 5 (adjoint quadruple, factorization systems, base change, cartesian closure) is not implemented — it's structural rather than modeling-oriented.

## What's new in v0.3 (Extensions v2)

The v0.3 release closes the categorical gaps surfaced by downstream PolyCDS work. Highlights:

- **`BicomoduleMorphism`** — first-class 2-cells in Cat#. Vertical and horizontal composition, whiskering, structural validation matching `validate_bicomodule_detailed`'s failure shape.
- **Kan extensions** — `kan_along_bicomodule` (finite, comodule-along-bicomodule) and `kan_2cat` (symbolic-aware, 2-categorical Kan), both returning a `KanExtension` record with `factor_through` for the universal property. Identity-D case ships in v0.3; non-identity in v0.3.x. See [`docs/dev/kan_extensions_construction.md`](docs/dev/kan_extensions_construction.md).
- **`support` operator** — Fairbanks-style support of `PolyElement(p, position, assignment)` for the concrete case; `free_variables` on `SymExpr` for the symbolic side.
- **Authoring helpers** — `bicomodule_from_data` / `comonoid_from_data` build the underlying lenses from authored Dicts. Validates by default; `validate=false` for intermediate constructions. Walkthrough at [`docs/src/tours/08_bicomodule_walkthrough.md`](docs/src/tours/08_bicomodule_walkthrough.md).
- **`LazyCofreeComonoid`** — defers the tower-of-exponentials `behavior_trees` enumeration. Cached materialization, `tree_at` for single-tree access, lazy `validate_comonoid` via Niu/Spivak Thm 8.45.
- **Inspection** — `back_directions(L::Lens)` returns a `BackDirectionTable` (or callable above `TABULATE_SIZE_CAP`). `sharp_L` / `sharp_R` shorthands for bicomodules; pretty `show` per position groups for fast eyeballing.
- **Soft API break** — `⊗(::Comonoid, ::Comonoid)` is now the carrier-tensor (matching `Polynomial ⊗`); v0.2 callers expecting categorical product should switch to `*`. See [`docs/dev/extensions_v2_design.md`](docs/dev/extensions_v2_design.md) §1.

The full design doc with all 28 resolved questions and the implementation phasing is at [`docs/dev/extensions_v2_design.md`](docs/dev/extensions_v2_design.md).

## Two flavors

The library has two layers that interoperate:

**Concrete layer.** `Polynomial`, `Lens`, etc. — actual data, finite enumeration. Use this when you have explicit position-sets and direction-sets and want to compute. Operations like `subst(p, q)` eagerly enumerate.

**Symbolic layer.** `SymbolicPolynomial`, `SymbolicLens` — variable-driven expression trees with `simplify` and a rewrite-rule engine. Use this when you're working up to isomorphism, want to verify book identities like `(a + b) ⊗ c ≈ (a ⊗ c) + (b ⊗ c)`, or y