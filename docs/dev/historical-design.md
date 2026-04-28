> **Historical** — this is the original Sprint 1 design plan from 2026-04.
> The library has shipped through Sprint 8 and diverged in places (the
> book's `◁` became `▷` in Julia syntax, we built standalone instead of on
> Catlab.jl, the visualization story moved to a sibling `PolyViz` package).
> For current state, see `README.md` at the repo root and the Documenter
> site under `docs/`. Kept for reference, not as a maintained spec.

---

# Poly.jl — Design Plan

A Julia library implementing the category **Poly** of polynomial functors, dependent lenses, and the structures built on top — following Niu & Spivak's *Polynomial Functors: A Mathematical Theory of Interaction* (2024). Built on Catlab.jl / AlgebraicJulia.

This document is a **plan**, not code. Read it, push back on choices, then we'll start writing.

---

## 0. Goals and non-goals

**In scope (per the book):**

1. Polynomial functors `p ≅ Σ_{i ∈ p(1)} y^{p[i]}` as objects.
2. Dependent lenses `f : p → q` (= morphisms in **Poly**).
3. The four monoidal structures: coproduct `+`, cartesian product `×`, parallel/Dirichlet product `⊗`, composition product `◁`.
4. Closure `[q, r]` of `⊗`, with evaluation lens.
5. Sections `Γ(p)`, the bundle, derivatives.
6. Dependent dynamical systems `Sy^S → p` (Moore machines, automata, robots, wiring patterns).
7. Comonoids in `(Poly, y, ◁)` ↔ small categories (Ahman–Uustalu). Retrofunctors as morphisms. The category **Cat#**.
8. Cofree comonoid `T_p` (trees on `p`, paths as morphisms).
9. Comodules and bicomodules; bicomodules ↔ prafunctors.
10. Vertical-cartesian and epi-mono factorizations of lenses; cartesian-closure of Poly; adjoint quadruple with Set.

**Out of scope (initially):**

- Multi-variable polynomial functors (book only treats single-variable; multi-variable arises via comodules — that's already covered by item 9).
- Performance-critical numerical simulation. The library is mathematical/symbolic first; Moore-machine *simulation* is supported, but the goal is correctness and ecosystem integration over speed.
- Persistent state, IO, GUIs.

**Quality bar:** every chapter's running examples (Example 2.4, 3.10, 3.14, 4.2, 4.6, 4.7, 4.30, 4.49, 4.51, 6.27, 7.23, 7.34, 8.10, etc.) should be expressible and verifiable in the library.

---

## 1. Catlab.jl integration: what to reuse, what to extend

Catlab supplies the category-theoretic substrate. We build *on top of* it rather than parallel to it.

### What Catlab already provides we should use

| Catlab piece | Role in Poly.jl |
|---|---|
| `FinSet` (and friends) | Concrete finite sets — first realization of position-set / direction-set. |
| `FinFunction` | Concrete functions between FinSets — the building block of on-positions and on-directions functions in finite cases. |
| `Category` / `@instance` GAT machinery | Define **Poly** itself as a `@instance Category`. |
| `MonoidalCategory`, `SymmetricMonoidalCategory`, `MonoidalCategoryWithDiagonals` (in `Catlab.Theories`) | We get `+`, `×`, `⊗` essentially for free as instances; we'll need to add a custom theory for `◁` (asymmetric). |
| `CartesianClosed` theory | Existing theory for `(×, ^)`; we use it for Theorem 5.31 (Poly is cartesian closed). |
| `Comonoid` theory | If present, instance it for `(Poly, y, ◁)`. Otherwise define our own theory `@theory ThComonoid`. |
| `FinDomFunction`, `TypeSet` | When direction-set domains are typed (e.g. `Int`, `String`) but not enumerable. |
| Catlab's `Diagram` and limits/colimits machinery | For `tree_p` as a limit (Prop 8.18). |
| `ACSets` | A natural representation of small categories ⇒ a natural "category as ACSet" path that interoperates with Cat#. |

### What we'll have to add

1. A `PolySet` abstract type generalizing `FinSet` to admit symbolic / opaque sets (see §2).
2. A `Polynomial` type and its instances of `Category`, `MonoidalCategory`, etc.
3. The composition product `◁` (no direct Catlab equivalent — it's the *substitution* monoidal product).
4. The closure `[q, r]` (an internal hom for `⊗`).
5. `Cat#` as a category whose objects wrap polynomial comonoids and morphisms are retrofunctors.
6. `Tree` / cofree-comonoid construction (limits in Poly, plus tree algebra).
7. Polybox rendering (a `show(::IO, ::MIME"text/plain", ::Lens)` that draws the polybox or corolla picture — useful, not critical).

We should **not** redefine `Category`, `Functor`, `MonoidalProduct` etc. — we *instance* the existing GATs.

---

## 2. The set abstraction: how `p[i]` and `p(1)` are represented

This is the central representation question. The book ranges from `2`, `N`, `R²`, `[0, 1]` to opaque sets `S`, `A`, `I`. The library has to handle all of this with consistent operations.

### Proposed type hierarchy

```
abstract type PolySet end

# Catlab-backed concrete finite sets (cardinality known, elements enumerable)
struct FinPolySet <: PolySet
    fs::FinSet            # wraps Catlab's FinSet
end

# Range-style sets for natural numbers, intervals, etc. — known structure but maybe infinite
struct IntervalSet{T} <: PolySet  # e.g. (0,20], [0,∞)
    a::T; b::T
    a_open::Bool; b_open::Bool
end

struct NatSet <: PolySet end       # ℕ
struct IntSet <: PolySet end       # ℤ
struct RealSet <: PolySet end      # ℝ
struct ProductSet{T<:Tuple} <: PolySet
    factors::T
end
struct SumSet{T<:Tuple} <: PolySet
    summands::T
end
struct ExpSet <: PolySet           # X^A
    base::PolySet; exp::PolySet
end

# Opaque symbolic sets — known by name only
struct SymbolicSet <: PolySet
    name::Symbol
    cardinality::Union{Cardinality, Nothing}  # optional metadata
end
```

### Operations on `PolySet`

A small algebra:
- `Base.eltype(::PolySet)` — element type, when meaningful.
- `Base.iterate(::PolySet)` — enumeration, when finite.
- `Base.length(::PolySet)` / `cardinality(::PolySet)` — size; may return `Cardinality.Finite(n)`, `Cardinality.CountablyInfinite()`, `Cardinality.Continuum()`, or `Cardinality.Symbolic(name)`.
- `Base.in(x, s::PolySet)` — membership. Defined for finite/range/concrete; falls back to `error` or symbolic for opaque.
- Smart constructors: `polyset(::FinSet)`, `polyset(1:10)`, `polyset(Int)` for `IntSet`, etc. Convenience `@polyset` macro.
- Coproduct/product/exp: `s + t`, `s × t`, `s^t` return `PolySet`. Used directly when computing `(p+q)[i]`, `(p×q)[i]`, etc.

### Functions between `PolySet`s

```
abstract type PolyFunction end

struct ConcreteFunction <: PolyFunction
    dom::PolySet; cod::PolySet
    f::Function   # for FinPolySet, can be eagerly tabulated
end

struct SymbolicFunction <: PolyFunction
    dom::PolySet; cod::PolySet
    name::Symbol
    formula::Union{Expr, Nothing}
end

struct DependentFunction <: PolyFunction
    dom::PolySet
    cod_at::Function    # i ↦ PolySet
    f::Function         # i ↦ element of cod_at(i)
end

# Operators
∘(g, f), id(s), constfn(s, t, x), ...
```

A key invariant: when both `dom` and `cod` are finite, `ConcreteFunction` is fully tabulated and equality is decidable. For symbolic ones, equality is structural / by name.

### Why this hierarchy

It mirrors how the book actually uses sets:
- Most worked examples use finite enumerable sets ⇒ `FinPolySet`.
- Counter, real-plane robot, intervals (Caroline & parents) ⇒ `IntervalSet` / `NatSet` / `RealSet`.
- All theoretical statements ("for any set S") ⇒ `SymbolicSet`.

You can build a polynomial that mixes these (`{open}y^{coins} + {closed}` — `open/closed/coins` finite), and the library should not force you to evaluate symbolic things to make progress on concrete things.

---

## 3. Module / file layout

```
Poly.jl                              # umbrella, re-exports
src/
├── Poly.jl                          # module root
├── sets/
│   ├── PolySets.jl                  # PolySet hierarchy (§2)
│   ├── PolyFunctions.jl             # PolyFunction hierarchy
│   └── DependentFunctions.jl        # (i ∈ I) → X(i)
├── core/
│   ├── Polynomial.jl                # Polynomial type
│   ├── Lens.jl                      # Lens type, identity, composition
│   ├── SpecialClasses.jl            # constant, linear, monomial, representable
│   ├── Sections.jl                  # Γ(p), the bundle, do-nothing section
│   └── Derivative.jl                # ṗ, the canonical p·y → p
├── monoidal/
│   ├── Coproduct.jl                 # +
│   ├── Product.jl                   # ×
│   ├── Parallel.jl                  # ⊗
│   ├── Composition.jl               # ◁
│   ├── Closure.jl                   # [q, r] for ⊗
│   └── DayConvolution.jl            # general ⊙ from Set monoidal structure
├── categorical/
│   ├── PolyCategory.jl              # @instance Category for Poly
│   ├── PolyMonoidal.jl              # @instances for +, ×, ⊗
│   ├── PolyComposition.jl           # custom theory for ◁ (asymmetric)
│   ├── PolyCartesianClosed.jl       # exponentials; Theorem 5.31
│   ├── Adjunctions.jl               # Set/Poly adjoint quadruple, base change
│   ├── Factorizations.jl            # epi-mono and vertical-cartesian
│   └── LimitsColimits.jl            # general (co)limits
├── dynamical/
│   ├── DynamicalSystem.jl           # type alias Sy^S → p
│   ├── MooreMachine.jl              # Iy^A interface specialization
│   ├── Automaton.jl                 # halting / non-halting DSAs
│   ├── Combinators.jl               # juxtapose, wrap, section
│   ├── InteractionPattern.jl        # ⊗_i p_i → q
│   └── Run.jl                       # Run_n via δ⁽ⁿ⁾ once comonoids land
├── comonoid/
│   ├── Comonoid.jl                  # (𝔠, ε, δ) struct + laws
│   ├── Category.jl                  # Comonoid ↔ small category translation
│   ├── Retrofunctor.jl              # comonoid morphisms
│   ├── Cofree.jl                    # T_p, the cofree comonoid (Tree-based)
│   └── CatSharp.jl                  # @instance Category for Cat#
├── comodule/
│   ├── LeftComodule.jl
│   ├── RightComodule.jl
│   ├── Bicomodule.jl
│   └── Prafunctor.jl                # via Theorem 8.100
├── viz/
│   ├── Polyboxes.jl                 # plain-text and TikZ rendering
│   ├── CorollaForest.jl
│   └── TransitionDiagram.jl         # for dynamical systems / categories
└── examples/
    ├── coin_jar_owner.jl            # Ex 2.19, 3.10
    ├── caroline_parents.jl          # Ex 3.14
    ├── moore_clock.jl               # Ex 4.2
    ├── counter.jl                   # Ex 4.6
    ├── plane_robot.jl               # Ex 4.7
    ├── grid_robot.jl                # Ex 4.30
    ├── two_body.jl                  # Ex 4.49
    ├── chalk_pinch.jl               # Ex 4.51
    ├── walking_arrow.jl             # Ex 7.23 / 7.34
    └── arrow_field.jl               # Ex 7.71
test/
└── ...                              # one test file per chapter, mirroring book
```

The `examples/` folder doubles as integration tests and as documentation — every nontrivial example in the book should have a counterpart here.

---

## 4. Layer-by-layer API

The 8 layers from `poly_summary_for_julia_library.md` mapped to concrete types and functions.

### Layer 0–1: Polynomials

```julia
struct Polynomial
    positions::PolySet                       # p(1)
    direction_at::DependentFunction          # i ↦ p[i] as a PolySet
end

# Construction
Polynomial(positions, direction_at)
constant(I::PolySet)                         # I ≅ Iy⁰
linear(I::PolySet)                           # Iy
representable(A::PolySet)                    # y^A
monomial(I::PolySet, A::PolySet)             # Iy^A
y                                            # the identity polynomial
zero_poly                                    # 0 (initial in Poly)
one_poly                                     # 1 (terminal in Poly)

# Action on sets/functions
(p::Polynomial)(X::PolySet) -> PolySet       # Σ_i X^{p[i]}
(p::Polynomial)(f::PolyFunction) -> PolyFunction

# Predicates
is_constant(p), is_linear(p), is_monomial(p), is_representable(p)
positions(p), direction_at(p, i)             # accessors
total_directions(p)  # ṗ(1) = Σ_i p[i]

# Pretty-printing
"y^2 + 2y + 1"  Base.show formatting that recognizes special classes
```

### Layer 2: Lenses

```julia
struct Lens
    dom::Polynomial
    cod::Polynomial
    on_positions::PolyFunction                                   # f₁ : p(1) → q(1)
    on_directions::DependentFunction                             # i ↦ (q[f₁ i] → p[i])
end

# Construction
Lens(dom, cod, f₁, f♯)
identity_lens(p)
@lens p => q on_positions = ... on_directions = (i, b) -> ...   # macro for clarity

# Composition (vertical, ⨟)
compose(f::Lens, g::Lens)                    # also `f ⨟ g` if we steal an operator
Base.∘(g::Lens, f::Lens)                     # g ∘ f

# Application as natural transformation
(f::Lens)(X::PolySet) -> PolyFunction        # the X-component p(X) → q(X)

# Equality
==                                           # extensional on positions+directions when finite,
                                             # structural otherwise

# Lifting
to_natural_transformation(f::Lens)
```

### Layer 3: Monoidal structures

Each monoidal product gets a binary operator on `Polynomial`, and a corresponding binary on `Lens` (the bifunctor action).

```julia
# Coproduct (unit: zero_poly)
+(p::Polynomial, q::Polynomial) -> Polynomial
+(f::Lens, g::Lens) -> Lens

# Cartesian product (unit: one_poly)
×(p::Polynomial, q::Polynomial) -> Polynomial
×(f::Lens, g::Lens) -> Lens
*(p::Polynomial, q::Polynomial) = ×(p, q)    # convenience: pq notation

# Parallel / Dirichlet (unit: y)
⊗(p::Polynomial, q::Polynomial) -> Polynomial
⊗(f::Lens, g::Lens) -> Lens

# Composition product (unit: y, asymmetric)
◁(p::Polynomial, q::Polynomial) -> Polynomial
◁(f::Lens, g::Lens) -> Lens                  # horizontal composition
^(p::Polynomial, n::Integer) = ◁_n(p)        # n-fold composition (carefully, since ^ has other meanings)
```

Notable detail: `◁` on positions yields `Σ_i Σ_{j̄ : p[i] → q(1)} ...`, which is *not* enumerable when `p[i]` or `q(1)` is infinite. The library should:
- For finite/finite cases: build it eagerly.
- For mixed/infinite cases: keep `Σ_{j̄ : p[i] → q(1)}` as a *symbolic* sum-set (a `PolySet` that knows it's "the set of functions p[i] → q(1)") and only enumerate when asked.

Day convolution (Prop 3.79): a higher-order constructor

```julia
day_convolution(unit::PolySet, op::Function) -> (Polynomial, Polynomial) -> Polynomial
```

### Layer 4: Closure of `⊗`

```julia
internal_hom(q::Polynomial, r::Polynomial) -> Polynomial      # [q, r]
eval_lens(q::Polynomial, r::Polynomial) -> Lens               # [q, r] ⊗ q → r
curry(f::Lens) -> Lens                                        # (p ⊗ q → r) ↦ (p → [q, r])
uncurry(f::Lens) -> Lens                                      # inverse

# Useful identities exposed:
sections(p) -> PolySet                                        # Γ(p) = Poly(p, y)
hom_set(p::Polynomial, q::Polynomial) -> PolySet              # Poly(p, q) = [p, q](1)
```

### Layer 5: Dynamical systems

```julia
const StateSystem = Polynomial                                # for documentation
state_system(S::PolySet) = monomial(S, S)                     # Sy^S

const DynamicalSystem = Lens                                  # type alias
moore_machine(S, A, I, return_fn, update_fn) -> DynamicalSystem
section(γ::Lens)                                              # check γ.cod === y
do_nothing_section(S::PolySet) -> Lens                        # Sy^S → y, identity dependent function

# Combinators
juxtapose(systems::Vector{DynamicalSystem}) -> DynamicalSystem  # ⊗ of dynamical systems
wrap(φ::DynamicalSystem, f::Lens) -> DynamicalSystem            # post-compose
close(φ::DynamicalSystem, γ::Lens) -> DynamicalSystem           # γ : interface(φ) → y; result is a section
interaction_pattern(p_list, q, on_pos, on_dir) -> Lens

# Simulation
step(φ::DynamicalSystem, state, direction)                    # applies update; returns new state
trajectory(φ::DynamicalSystem, s0, directions)                # iterator of (state, position) pairs
```

### Layer 6: Comonoids and Cat#

```julia
struct Comonoid
    carrier::Polynomial
    eraser::Lens                                              # ε : 𝔠 → y
    duplicator::Lens                                          # δ : 𝔠 → 𝔠 ◁ 𝔠
end

# Validation
function validate_comonoid_laws(c::Comonoid;
    check_left_counit=true, check_right_counit=true, check_coassoc=true)
    # symbolic identity-of-lenses check; for finite carriers this is exhaustive,
    # for symbolic ones we rely on structural equality.
end

# Construction
state_system_comonoid(S::PolySet) -> Comonoid                 # Sy^S as comonoid
discrete_comonoid(S::PolySet) -> Comonoid                     # Sy
walking_arrow_comonoid() -> Comonoid                          # y² + y, Example 7.23
monoid_comonoid(M::PolySet, e, op) -> Comonoid                # y^M

# Translation: comonoid ↔ small category
to_category(c::Comonoid) -> SmallCategory                     # via Ahman-Uustalu
from_category(C::SmallCategory) -> Comonoid

# n-fold duplicator
duplicator_n(c::Comonoid, n::Int) -> Lens                     # δ⁽ⁿ⁾ : 𝔠 → 𝔠 ◁ⁿ

# Retrofunctor
struct Retrofunctor
    dom::Comonoid
    cod::Comonoid
    underlying::Lens                                          # 𝔠 → 𝔠'
    # invariants: underlying respects ε and δ
end

validate_retrofunctor_laws(F::Retrofunctor)
identity_retrofunctor(c::Comonoid) -> Retrofunctor
compose(F::Retrofunctor, G::Retrofunctor) -> Retrofunctor

# Cat# as a Catlab category
@instance Category{Comonoid, Retrofunctor} (CatSharp,) begin
    dom(F::Retrofunctor) = F.dom
    codom(F::Retrofunctor) = F.cod
    id(c::Comonoid) = identity_retrofunctor(c)
    compose(F, G) = compose(F, G)
end
```

The `SmallCategory` type can wrap Catlab's existing category data — likely as an `ACSet` schema like `FreeCategory`. We need a clean translation between our `Comonoid` and Catlab's `FinCat` so the same example can be expressed either way.

### Layer 7: Cofree comonoid

```julia
# A p-tree
abstract type PolyTree end                                    # may be infinite
struct PolyTreeNode <: PolyTree                               # eager, finite-depth
    position::Any                                             # ∈ p(1)
    children::Dict{Any, PolyTree}                             # p[position] → subtree
end
struct PolyTreeLazy <: PolyTree                               # corecursive / symbolic
    position::Any
    child_fn::Function                                        # direction ↦ PolyTree
end

# Cofree
cofree_comonoid(p::Polynomial) -> Comonoid                    # T_p
unfold_pretree(p::Polynomial, n::Int, root_strategy) -> PolyTree   # n-stage pretree
trim(t::PolyTree, n::Int) -> PolyTree                         # truncate to depth n

# The forgetful-cofree adjunction (Theorem 8.45)
cofree_adjunction_unit(c::Comonoid) -> Retrofunctor           # c → T_{U c}
cofree_adjunction_counit(p::Polynomial) -> Lens               # U T_p → p
```

### Layer 8: Comodules and bicomodules

```julia
struct LeftComodule
    comonoid::Comonoid                                        # C
    carrier::Polynomial                                       # m
    coaction::Lens                                            # λ : m → 𝔠 ◁ m
end

struct RightComodule
    comonoid::Comonoid                                        # D
    carrier::Polynomial                                       # m
    coaction::Lens                                            # ρ : m → m ◁ 𝔡
end

struct Bicomodule
    left::Comonoid
    right::Comonoid
    carrier::Polynomial
    left_coaction::Lens
    right_coaction::Lens
end

# Theorem 8.100
to_prafunctor(b::Bicomodule) -> Prafunctor
from_prafunctor(F::Prafunctor) -> Bicomodule

# Useful identifications
left_comodule_to_copresheaf(C::Comonoid, m::LeftComodule) -> Copresheaf  # Set^C
right_comodule_to_dopf(D::Comonoid, m::RightComodule)                     # discrete opfibration
```

---

## 5. Equality, normalization, and computation

The book talks about `≅` (isomorphism) far more often than `=` (equality). The library distinguishes:

- `==`: structural / definitional. Same struct fields. Cheap.
- `isiso(p, q)` / `isiso(f, g)`: a (possibly heuristic) isomorphism check. For finite polynomials, decidable. For symbolic ones, we provide a normalize-then-compare routine.
- `normalize(p::Polynomial)`: combine like-terms (e.g., `y² + y² + y → 2y² + y`), order summands canonically, simplify direction-sets.

For finite cases, lens equality reduces to `f₁` and all `f♯_i` being equal as `FinFunction`s — Catlab handles this. For symbolic cases we either check by symbolic identity or punt to the user.

A `@simp` macro expands shorthand like `y^3 + 2y + 1` to a canonical `Polynomial`.

---

## 6. The four monoidal products as Catlab GAT instances

Catlab has theories for several monoidal patterns. We instance them where they fit, and define a custom theory for `◁` since it's asymmetric and not a symmetric monoidal product.

```julia
@instance ThSymmetricMonoidalCategory{Polynomial, Lens} begin
    munit() = y                          # for ⊗
    otimes(p, q) = p ⊗ q
    otimes(f, g) = f ⊗ g
    braid(p, q) = ...                    # symmetry of ⊗
end

@instance ThCartesianCategory{Polynomial, Lens} begin
    munit() = one_poly                   # for ×
    otimes(p, q) = p × q
    pair(f, g) = ...                     # universal property
    proj1(p, q), proj2(p, q) = ...
end

@instance ThCocartesianCategory{Polynomial, Lens} begin
    mzero() = zero_poly                  # for +
    oplus(p, q) = p + q
    copair(f, g) = ...
    coproj1(p, q), coproj2(p, q) = ...
end

# Custom theory for the asymmetric composition product
@theory ThSubstitutionMonoidalCategory{Ob, Hom} <: ThCategory{Ob, Hom} begin
    sunit::Ob                                                       # y
    subst(p::Ob, q::Ob)::Ob                                         # p ◁ q
    subst(f::Hom(p, p'), g::Hom(q, q'))::Hom(subst(p, q), subst(p', q'))
    # left/right unitors and associator with sunit
end

@instance ThSubstitutionMonoidalCategory{Polynomial, Lens} begin
    sunit() = y
    subst(p, q) = p ◁ q
    subst(f, g) = f ◁ g
end
```

The duoidal-category structure between `(y, ⊗)` and `(y, ◁)` (Prop 6.87) becomes a separate `@theory ThDuoidalCategory` instance.

---

## 7. Validation strategy

Every layer comes with property-based tests asserting laws, plus concrete book examples as integration tests.

| Layer | Key invariants tested |
|---|---|
| Set | Distributive law (Prop 1.27); cardinality; set-as-functor laws |
| Polynomial | `p(1)` recovers position-set; `(p+q)(X) = p(X)+q(X)`; `p` reproduces book examples |
| Lens | Identity laws; associativity of vertical composition; `Poly(y^S, q) ≅ q(S)` (Yoneda); Prop 3.50 (commutative diagrams in Poly factor through positions and directions) |
| Monoidal (×, +, ⊗) | Coherence: unitors, associators, braiding; `× ≠ ⊗` for non-trivial cases; ⊗ distributes over + (Ex 3.77) |
| ◁ | Associativity; left/right unit; `p ◁ y ≅ p`; horizontal composition matches the formula in Ex 6.19 |
| Closure | Prop 4.85 adjunction (test via `curry/uncurry` round-trip); `Poly(p, q) ≅ [p, q](1)` |
| Dynamical | Moore machines reproduce expected trajectories (Ex 4.2 sequence; Ex 4.6 counter); juxtapose-then-section equals direct system; `Run_n` correctness against manual stepping |
| Comonoid | All three laws (left/right counit, coassoc) hold for built-ins (state-system, discrete, walking-arrow); `δ⁽ⁿ⁾` equals iterated δ |
| Comonoid ↔ Cat | Round-trip: `from_category(to_category(c)) ≅ c`; carrier and law translation matches Table in §7.2.1 |
| Retrofunctor | Three retrofunctor laws (preserves id, cod, composition); preserves isomorphisms (Prop 7.61); arrow-field example (Ex 7.71) |
| Cofree | Universal property: every retrofunctor `c → T_p` factors through unique lens `U c → p` |
| Comodule | Counit + coassoc; left-comodule = copresheaf (Prop 8.88) |

Run `Pkg.test()` end-to-end exercises ~30 book examples.

---

## 8. Examples roadmap (driven by the book)

A library-as-tutorial. Each example file should:
1. Define the relevant polynomials in idiomatic Julia.
2. Show the lens(es) the book builds.
3. Re-derive a result from the book and assert it programmatically.

Priority order (each unblocks the next):
1. `coin_jar_owner.jl` — basic polynomial + lens + interaction protocol.
2. `caroline_parents.jl` — polynomials over ℝ intervals, lens via formula.
3. `moore_clock.jl` — Moore machine, basic stepping, and reading off a trajectory.
4. `counter.jl` — the simplest `Sy^S → Iy^A` machine.
5. `grid_robot.jl` — dependent dynamical system; `(n×n)y^{n×n} → Σ_{i,j} y^{D_i × D_j}`.
6. `two_body.jl` — two systems with `⊗` and a section over them.
7. `walking_arrow.jl` — the smallest non-state-system comonoid (`y² + y`); validate Ex 7.23.
8. `arrow_field.jl` — retrofunctor `C ↛ y^N` (Ex 7.71). Cat# in action.
9. `cofree_run.jl` — given any `φ : Sy^S → p`, lift to `Sy^S ↛ T_p`. The "all-trajectories-at-once" example.

---

## 9. Resolved design decisions

Decided 2026-04-27:

**Q1 — `PolyFunction` representation: lazy by default, `tabulate(f)` on demand.** Single uniform type with a `Function` field. Works for symbolic inputs out of the box. Equality auto-tabulates when both sides are finite under a soft size cap (proposal: 10⁵ entries), and errors with a clear message otherwise.

**Q2 — Symbolic Cardinality algebra: yes.** Define a `Cardinality` type:
```julia
abstract type Cardinality end
struct Finite <: Cardinality; n::Int end
struct CountablyInfinite <: Cardinality end
struct Continuum <: Cardinality end
struct SymbolicCardinality <: Cardinality; name::Symbol end
```
with `+`, `×`, `^` defined among them. Every `PolySet` exposes `cardinality(::PolySet)::Cardinality`. Powers hom-set sizing (Example 3.15: `|Poly(p,q)| = 92 · 4 · 4 = 1472`) without enumeration.

**Q3 — `◁` on infinite positions: return a `SymbolicSet`.** `positions(p ◁ q)` for the general case returns a deferred set describing `Σ_i Σ_{j̄ : p[i] → q(1)} 1`. Concrete enumeration only on finite/finite. The `Cardinality` is computed symbolically via Q2.

**Q4 — Comonoid ↔ Category: hybrid.** `to_category(c::Comonoid)` returns Catlab `FinCat` when `c.carrier`'s position-set and direction-sets are all finite, an internal `SmallCategory` wrapper otherwise. Provide `Base.convert(FinCat, ::SmallCategory)` and the reverse, with a clear error when conversion isn't possible. From Catlab's side, `from_category(::FinCat) -> Comonoid` is the natural reverse.

**Q5 — Visualization: separate `PolyViz.jl`, treated as important.** Plain-text / ASCII polyboxes ship in core (no deps); rich graphics (Compose.jl, Luxor, TikZ) live in a `PolyViz.jl` companion package. Important — not deprioritized — because debugging needs visual feedback. Core exposes structural hooks (`to_diagram_data(::Lens)` returning a plain Julia data structure, `to_corolla_forest_data(::Polynomial)`, etc.) that PolyViz consumes; this means PolyViz isn't a hard dep of core but plugs in cleanly. Sprint plan: build the data-extraction hooks alongside each layer; build PolyViz.jl in parallel as a sibling package.

**Q6 — Operators *and* named functions.** Both `p ⊗ q` and `parallel(p, q)`; both `p ◁ q` and `compose_product(p, q)`; both `[q, r]` notation (via `Base.getindex`-as-internal-hom or a custom op) and `internal_hom(q, r)`. Document the operators in the README; named ones are tab-completable in IDEs.

**Q7 — Performance: revisit later.** Polynomials in practice will be built from symbolic or small finite sets, so the math-first single-type design suffices. No dense-Int-array specializations now. If a perf wall is ever hit, add specialized methods or a `PolyFast.jl` companion later.

**Q8 — Docs: Documenter.jl + Literate.jl.** API reference via Documenter; examples in `examples/*.jl` are Literate-compatible scripts that compile into runnable, tested, web-rendered tutorials. Standard AlgebraicJulia toolchain.

---

## 10. Sequencing — what we build first

Visualization is now distributed across sprints (per Q5) rather than saved for the end. Each sprint adds a renderer for the structures it introduces.

1. **Sprint 1 (Foundation).** `PolySet` hierarchy with `Cardinality` algebra; `PolyFunction` (lazy + `tabulate`); `Polynomial` and special classes; `show` for `Polynomial`. Acceptance: `y² + 2y + 1` round-trips; `p(X)` matches Example 2.4 for `X = {a, b}`; `cardinality(y^A ⊗ y^B)` returns `|A| × |B|` symbolically.

2. **Sprint 2 (Lenses + corolla forests).** `Lens` type, identity, vertical composition, equality on finite cases. ASCII polybox renderer. Compose.jl corolla-forest renderer. Acceptance: Example 3.10 (coin jar + owner) builds; Example 3.15 lens count verified (1472 lenses); polyboxes for the lens render correctly.

3. **Sprint 3 (Monoidal: +, ×, ⊗).** Three operations on polynomials and lenses; `@instance` declarations for the existing Catlab GAT theories. Acceptance: Example 3.62, 3.70; `⊗` distributes over `+` (Ex 3.77); corolla forests for `pq` and `p ⊗ q` rendered.

4. **Sprint 4 (Composition product `◁`).** `◁` for polynomials and lenses; custom `ThSubstitutionMonoidalCategory` theory; symbolic positions when infinite. Compose.jl height-n tree rendering for `p ◁ q`. Acceptance: Examples 6.27, 6.31; `p ◁ y ≅ p` and `y ◁ p ≅ p`; `(y² + y) ◁ (y³ + 1) ≅ y⁶ + 3y³ + 2`.

5. **Sprint 5 (Closure & sections).** `[q, r]`, `eval_lens`, `Γ`, `do_nothing_section`. Acceptance: Prop 4.54 holds; Example 4.81 identities; `Poly(p, q) ≅ [p, q](1)`.

6. **Sprint 6 (Dynamical systems + transition diagrams).** Moore machines, dependent dynamical systems, juxtapose/wrap/section. Stepping & trajectories. Compose.jl labeled-transition-diagram renderer. Acceptance: Example 4.2 reproduces the (orange, orange, green, orange, …) → (1, 0, 0, 1, 0, …) sequence; grid robot moves correctly; transition diagrams for Examples 4.2, 4.24, 4.36 render.

7. **Sprint 7 (Comonoids + Cat#).** `Comonoid` struct, laws, ↔ `FinCat`/`SmallCategory` translation (Q4), `δ⁽ⁿ⁾`, retrofunctors, `Cat#` as `@instance Category`. Acceptance: walking-arrow round-trips; arrow-field example (Ex 7.71) implemented.

8. **Sprint 8 (Cofree comonoid).** `tree_p`, `T_p`, the cofree-forgetful adjunction. Acceptance: every dynamical system lifts to a retrofunctor into `T_p`; Example 8.52 (running a system as a single retrofunctor).

9. **Sprint 9 (Comodules).** Left/right/bi comodules; prafunctor identification (Theorem 8.100). Acceptance: copresheaf ↔ left comodule round-trip on a small example.

10. **Sprint 10 (TikZ output, docs, registration).** TikZ renderers for polyboxes, corolla forests, transition diagrams. Documenter.jl + Literate.jl docs site (Q8). README, license, package registration in JuliaHub.

Sprints 1–4 are the spine — even if we stop there we have a usable polynomial-functor library. 5–6 give the full dynamical-systems story (which is the most-applicable bit for modeling). 7–9 are the deep categorical layer. 10 is the QOL pass.

---

## What I'd like from you next

Q1–Q8 are now resolved in §9. The two big calls — set abstraction (§2) and Catlab integration (§6) — should be the next things you eyeball before we start coding, since they ripple through everything.

When you're happy with §2 and §6, I'll start Sprint 1.
