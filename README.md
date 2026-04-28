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

Plus a parallel symbolic layer (`SymbolicPolynomial`, `SymbolicLens`, ~25 rewrite rules with trace mode), a `@poly` macro, and a LaTeX renderer. Chapter 5 (adjoint quadruple, factorization systems, base change, cartesian closure) is not implemented — it's structural rather than modeling-oriented.

## Two flavors

The library has two layers that interoperate:

**Concrete layer.** `Polynomial`, `Lens`, etc. — actual data, finite enumeration. Use this when you have explicit position-sets and direction-sets and want to compute. Operations like `subst(p, q)` eagerly enumerate.

**Symbolic layer.** `SymbolicPolynomial`, `SymbolicLens` — variable-driven expression trees with `simplify` and a rewrite-rule engine. Use this when you're working up to isomorphism, want to verify book identities like `(a + b) ⊗ c ≈ (a ⊗ c) + (b ⊗ c)`, or your sets are infinite/symbolic. `lift` and `evaluate(env)` bridge the two layers.

The two flavors share notation: `+`, `*` (alias `×`), `⊗`/`parallel`, and `▷`/`subst` work on both `Polynomial` and `SymbolicPolynomial` via Julia dispatch.

## Equality conventions

`==` is **strict structural** equality — same position-set elements, same direction-sets per position. So `p × q != q × p` because the position-tuples come out in a different order.

`≈` (alias for `is_iso`) is **cardinality-iso** — same shape up to relabeling. So `p × q ≈ q × p` and most book identities are stated with `≈`.

`is_iso_strict(p, q)` is in between: a structural bijection that respects direction-sets exactly (distinguishes `Ny` from `Ry`).

For symbolic expressions, `sym_equal(a, b)` simplifies both sides and compares.

## Composition product: `◁` vs `▷`

The book writes `◁` (U+25C1) for the substitution / composition product. Julia's parser does not accept that character as an infix operator, so we use `▷` (U+25B7) at multiplication precedence:

```julia
p ▷ q              # = subst(p, q),   read "p ◁ q"
subst_n(p, n)      # = p ◁ⁿ
```

Display strings, comments, and book references all still say `◁`. The discrepancy is a Julia-parser limitation, not a design choice.

## Comonoids in `(Poly, y, ▷)`

A comonoid in `(Poly, y, ▷)` is exactly a small category (Ahman–Uustalu). Three built-ins:

- `state_system_comonoid(S)` — the contractible groupoid on `S`.
- `discrete_comonoid(S)` — the discrete category with only identity morphisms.
- `monoid_comonoid(M, e, op)` — the one-object category `BM`.

`validate_comonoid(c)` checks the laws via the category translation by default. Pass `mode=:lens` to inspect the four book laws on the raw lens data instead — useful when debugging a hand-constructed comonoid.

## Documentation

- [Stable docs](https://aidanpetro1.github.io/Poly.jl/stable/) — full API reference plus three guided tours (polynomials and lenses, dynamical systems, comonoids = categories).
- [`docs/literate/`](docs/literate/) — the tour sources as runnable `.jl` files, processed by Literate.jl.

## Tests and demos

`test/runtests.jl` runs ~380 tests across all sprints:

```sh
julia --project=. -e 'using Pkg; Pkg.test()'
```

`examples/run_all_demos.jl` runs the `_sprintN_demo()` functions in sequence — they double as living examples.

## References

Niu, N. and Spivak, D. I. *Polynomial Functors: A Mathematical Theory of Interaction*. 2024. <https://github.com/ToposInstitute/poly>

Ahman, D. and Uustalu, T. *Directed Containers as Categories*. 2016. (The categorical correspondence used in Sprint 7.)

## License

MIT. See [LICENSE](LICENSE).
