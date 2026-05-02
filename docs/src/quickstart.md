# Quick start

## Loading the library

The library is not yet registered. Use it from the working tree:

```julia
include("src/Poly.jl")
using .Poly
```

For development on the docs site or `PolyViz`, each subdirectory has its own `setup.jl` that links `Poly` as a development dep.

## Hello, polynomial

```julia
p = @poly y^2 + 2y + 1            # 4 positions: y^2 · 1, y · 2, 1 · 1
cardinality(p.positions)          # Finite(4)
cardinality(p(FinPolySet([:a]))) # |p({:a})| = 4
```

## Building polynomials with `@poly`

The `@poly` macro lets you write polynomials in their standard mathematical
notation. Positions get anonymous integer labels; direction-sets become
`FinPolySet(1:k)`. Use the explicit `Polynomial(positions, dir_at_fn)`
constructor when you need meaningful labels.

```julia
@poly y                  # the identity polynomial
@poly y^3                # representable y^3 (one position, 3 directions)
@poly 2y                 # linear with 2 positions, each with 1 direction
@poly 0                  # the zero polynomial
@poly 1                  # the constant polynomial 1 (= y^0)

# Composite expressions:
@poly y^3 + 2y + 1       # mixed; 4 positions
@poly 2y^3               # 2 copies of y^3

# Tensor (Dirichlet / parallel product):
@poly y^2 ⊗ y^3          # = parallel(y^2, y^3) ≈ y^6

# Substitution (composition product):
@poly y^3 ▷ y^2          # = subst(y^3, y^2) ≈ y^6
@poly (y + 1) ▷ y^2      # left distributivity etc.

# Variables in scope on the right pass through unchanged:
q = @poly y + 1
@poly y^2 ▷ q            # composes with the bound `q`
```

`@poly`-built polynomials use integer labels, while the canonical
constants `y`, `zero_poly`, and `one_poly` use `Symbol` labels. They are
isomorphic but not `==`. Compare across forms with `≈` (alias for
`is_iso`):

```julia
@poly y    ≈ y           # true (cardinality-iso)
@poly y    == y          # false (different label types)
```

For unary minus or any operator the macro doesn't recognize, the macro
errors out — `@poly` is intentionally narrow. Reach for the explicit
`Polynomial(positions, dir_at_fn)` constructor when you outgrow it.

## Hello, lens

```julia
q = @poly y + 1
f = Lens(p, q,
         i -> i == 1 ? 1 : 2,         # on positions
         (i, b) -> :pt)                # on directions: vacuous when q-direction is empty
println(polybox(f; entries=(2, :pt)))
```

## Hello, Moore machine

```julia
S = FinPolySet([:a, :b])
A = FinPolySet([:up, :down])
I = FinPolySet([0, 1])
φ = moore_machine(S, I, A,
                  s -> s == :a ? 0 : 1,
                  (s, _) -> s == :a ? :b : :a)

output_trajectory(φ, :a, [:up, :up, :down])  # [0, 1, 0, 1]
```

## Hello, comonoid

```julia
S = FinPolySet([:x, :y, :z])
c = state_system_comonoid(S)
C = to_category(c)
@assert validate_comonoid(c)
@assert C.composition[((:x, :y), (:y, :z))] == (:x, :z)
```

## Symbolic side

```julia
a, b, c = sympoly(:a), sympoly(:b), sympoly(:c)
expr = parallel(a + b, c)
println(simplify(expr))             # a ⊗ c + b ⊗ c
sym_equal(parallel(a + b, c),
          parallel(a, c) + parallel(b, c))   # true
```
