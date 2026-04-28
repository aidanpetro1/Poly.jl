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
