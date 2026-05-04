# ============================================================
# Dynamical systems (Sprint 6)
# ============================================================
#
# A (dependent) dynamical system in Niu/Spivak Chapter 4 is a lens
#
#     φ : Sy^S → p
#
# where `Sy^S` is the *state system* on a state-set `S` and `p` is the
# *interface* polynomial. The on-positions function `φ₁ : S → p(1)` is the
# return function (output at each state); the on-directions map
# `φ♯_s : p[φ₁ s] → S` is the update function (next-state given current
# state and a chosen direction at the current output).
#
# A Moore machine is the special case `p = Iy^A` (monomial interface):
# every state takes the same set `A` of inputs and emits an `I`-valued output.
#
# This file provides ergonomic constructors and stepping/trajectory helpers.
# We don't introduce a `DynamicalSystem` struct — a system is just a `Lens`
# whose `dom` has the shape `Sy^S`.

# ============================================================
# Constructors
# ============================================================

"""
    state_system(S::PolySet) -> Polynomial

The state system on `S`: the polynomial `Sy^S` (monomial with `S` positions
and `S` directions at each position). This is the natural shape for a
dynamical system's *domain*.
"""
state_system(S::PolySet) = monomial(S, S)

"""
    is_state_system(p::Polynomial) -> Bool

True iff `p` looks like `Sy^S` for some set `S`: a monomial whose direction
cardinality equals its position cardinality.
"""
function is_state_system(p::Polynomial)
    is_monomial(p) || return false
    cardinality(p.positions) == cardinality(direction_at(p, first(p.positions)))
end

# Fallback for the widened `Lens.dom::AbstractPolynomial` (v0.4.x lazy
# sweep). Lazy variants like `LazySubst` are never state systems by
# construction (they're substitution polynomials, not monomials), so the
# answer is unconditionally false. Dispatching here keeps callers like
# `Coalgebra(::Lens)` from raising MethodError when handed a lens with a
# non-concrete dom.
is_state_system(::AbstractPolynomial) = false

"""
    moore_machine(S::PolySet, I::PolySet, A::PolySet, return_fn, update_fn) -> Lens

Build a Moore machine `Sy^S → Iy^A` from explicit return and update
functions:
- `return_fn(s)` for `s ∈ S` returns the output at state `s` (an element of `I`).
- `update_fn(s, a)` for `s ∈ S` and `a ∈ A` returns the next state in `S`.
"""
function moore_machine(S::PolySet, I::PolySet, A::PolySet,
                       return_fn::Function, update_fn::Function)
    Lens(state_system(S), monomial(I, A), return_fn, update_fn)
end

"""
    dynamical_system(S::PolySet, interface::Polynomial, return_fn, update_fn) -> Lens

Build a dependent dynamical system `Sy^S → interface`. Directions available
at each state depend on the position the system displays at that state, so
`update_fn(s, a)` is called with `a ∈ interface[return_fn(s)]`.
"""
function dynamical_system(S::PolySet, interface::Polynomial,
                          return_fn::Function, update_fn::Function)
    Lens(state_system(S), interface, return_fn, update_fn)
end

"""
    initial_state(S::PolySet, s0) -> Lens

The lens `y → Sy^S` corresponding to the choice of an initial state
`s0 ∈ S`. Composing this with a dynamical system `φ : Sy^S → p` is the
Niu/Spivak way of "starting the run" at a specific state.
"""
function initial_state(S::PolySet, s0)
    Lens(y, state_system(S), _ -> s0, (_i, _b) -> :pt)
end

# ============================================================
# Stepping and trajectories
# ============================================================

"""
    step(φ::Lens, state, direction)

Advance `φ` by one step from `state` given `direction` (an element of the
direction-set at the position currently returned by the system). Returns
the new state.

Implemented as a method on `Base.step` so it composes with Julia's existing
function — `step(0:5)` still works for ranges, and `step(φ, :b, :o)` does
the dynamical-system thing.
"""
function Base.step(φ::Lens, state, direction)
    φ.on_directions.f(state).f(direction)
end

"""
    trajectory(φ::Lens, s0, directions::AbstractVector) -> Vector

The list of states visited starting from `s0` and applying each direction
in sequence: `[s0, step(φ, s0, d1), step(φ, s1, d2), ...]`. Length is
`length(directions) + 1`.
"""
function trajectory(φ::Lens, s0, directions::AbstractVector)
    states = Any[s0]
    s = s0
    for d in directions
        s = step(φ, s, d)
        push!(states, s)
    end
    states
end

"""
    output_trajectory(φ::Lens, s0, directions::AbstractVector) -> Vector

The sequence of returned positions (Moore-machine outputs) the system
emits along the trajectory. Length is `length(directions) + 1` — one more
than the number of inputs, since we emit at the start state too.
"""
function output_trajectory(φ::Lens, s0, directions::AbstractVector)
    s = s0
    outs = Any[φ.on_positions.f(s)]
    for d in directions
        s = step(φ, s, d)
        push!(outs, φ.on_positions.f(s))
    end
    outs
end

"""
    state_output_trajectory(φ::Lens, s0, directions::AbstractVector) -> Vector{Tuple}

Like [`trajectory`](@ref) but each element is a `(state, output)` pair.
"""
function state_output_trajectory(φ::Lens, s0, directions::AbstractVector)
    s = s0
    log = Tuple[(s, φ.on_positions.f(s))]
    for d in directions
        s = step(φ, s, d)
        push!(log, (s, φ.on_positions.f(s)))
    end
    log
end

# ============================================================
# Combinators (mostly aliases for clarity)
# ============================================================

"""
    juxtapose(systems::Lens...) -> Lens

The parallel composite of dynamical systems. State-set is the product of
the constituent state-sets; interface is the parallel product of the
constituent interfaces. Just an alias for repeated `parallel`.
"""
juxtapose(systems::Lens...) = reduce(parallel, systems)

"""
    wrap(φ::Lens, f::Lens) -> Lens

Wrap an interface around a dynamical system: given `φ : Sy^S → p` and
`f : p → q`, returns `φ ⨟ f : Sy^S → q`. Just `compose(φ, f)`.
"""
wrap(φ::Lens, f::Lens) = compose(φ, f)

# ============================================================
# First-class Coalgebra (Extensions v1, PR #4)
# ============================================================
#
# A p-coalgebra in the sense of Niu/Spivak is a state space `S` (a PolySet)
# equipped with a structure map `α : Sy^S → p` (a lens). The library has
# carried these as plain lenses since Sprint 6; the `Coalgebra` struct
# gives them a peer-type identity alongside `Comonoid` and `Bicomodule`,
# with shape-only validation and a morphism type for the commuting-square
# condition.
#
# Important distinction: a `Coalgebra` here is a coalgebra of an
# *endofunctor* `p`. Comodules (`RightComodule`, `LeftComodule`,
# `Bicomodule`) satisfy counit and coassociativity laws against a
# comonoid's eraser and duplicator; coalgebras-of-functors carry only a
# structure map, with no laws beyond shape.

"""
    Coalgebra(carrier::PolySet, polynomial::Polynomial, structure::Lens)

A `polynomial`-coalgebra on state space `carrier`. The `structure` lens
`Sy^carrier → polynomial` encapsulates the "step" data: at each state
`s`, its `on_positions` returns the position of `polynomial` displayed
by `s`, and at direction `d ∈ polynomial[that position]`,
`on_directions(s, d)` returns the next state.

# Construction

```julia
Coalgebra(carrier, polynomial, structure)   # full constructor
Coalgebra(structure::Lens)                  # infer carrier from structure.dom
```

The full constructor type-checks shape; the inferred form requires
`structure.dom` to be of the form `Sy^S` (use [`is_state_system`](@ref)
to test).

# Relationship to existing dynamical-system constructors

`state_system`, `dynamical_system`, and `moore_machine` continue to return
`Lens` directly — that API is preserved for back-compat. Wrap any of
them in `Coalgebra(::Lens)` if you want the typed object, or use
[`moore_machine_coalgebra`](@ref) as a one-shot constructor.
"""
struct Coalgebra
    carrier::PolySet
    polynomial::Polynomial
    structure::Lens
    function Coalgebra(carrier::PolySet, polynomial::Polynomial, structure::Lens)
        expected_dom = state_system(carrier)
        structure.dom == expected_dom ||
            error("Coalgebra: structure.dom ≠ state_system(carrier) = Sy^$carrier; " *
                  "got $(structure.dom)")
        structure.cod == polynomial ||
            error("Coalgebra: structure.cod ≠ polynomial; got $(structure.cod), " *
                  "expected $polynomial")
        new(carrier, polynomial, structure)
    end
end

"""
    Coalgebra(structure::Lens) -> Coalgebra

Infer the `carrier` from `structure.dom` (which must be `Sy^S` for some
`S`) and use `structure.cod` as the polynomial. Errors if `structure.dom`
isn't a state system.
"""
function Coalgebra(structure::Lens)
    is_state_system(structure.dom) ||
        error("Coalgebra(::Lens): structure.dom is not Sy^S; use the full " *
              "Coalgebra(carrier, polynomial, structure) constructor")
    carrier = structure.dom.positions
    Coalgebra(carrier, structure.cod, structure)
end

function show(io::IO, c::Coalgebra)
    print(io, "Coalgebra(carrier=")
    show(io, c.carrier)
    print(io, ", polynomial=")
    show(io, c.polynomial)
    print(io, ")")
end

"""
    to_lens(c::Coalgebra) -> Lens

Recover the underlying structure lens. Inverse of `Coalgebra(::Lens)`
when the lens has a state-system domain.
"""
to_lens(c::Coalgebra) = c.structure

"""
    validate_coalgebra(c::Coalgebra) -> Bool

Shape-only check: verify `c.structure` has the right domain and codomain
shape for a `c.polynomial`-coalgebra on `c.carrier`. Coalgebras of an
endofunctor have no laws beyond shape, so this is strictly a shape check.

(The constructor already enforces the same invariants — this function
is useful when you've mutated something or built a coalgebra through a
non-default path.)

For the structured-result form, see [`validate_coalgebra_detailed`](@ref).
"""
validate_coalgebra(c::Coalgebra) = validate_coalgebra_detailed(c).passed

"""
    validate_coalgebra_detailed(c::Coalgebra) -> ValidationResult

Same shape check as [`validate_coalgebra`](@ref), with structural
failure information.
"""
function validate_coalgebra_detailed(c::Coalgebra)
    failures = ValidationFailure[]
    expected_dom = state_system(c.carrier)
    if c.structure.dom != expected_dom
        push!(failures, ValidationFailure(
            :coalgebra_domain, (),
            "structure.dom must be state_system(carrier) = Sy^$(c.carrier); " *
            "got $(c.structure.dom) — domain doesn't match the declared state space",
            c.structure.dom, expected_dom))
    end
    if c.structure.cod != c.polynomial
        push!(failures, ValidationFailure(
            :coalgebra_codomain, (),
            "structure.cod must equal polynomial; got $(c.structure.cod), " *
            "expected $(c.polynomial) — codomain doesn't match the declared endofunctor",
            c.structure.cod, c.polynomial))
    end
    isempty(failures) ? pass("coalgebra shape") : fail(failures)
end

"""
    moore_machine_coalgebra(S, I, A, return_fn, update_fn) -> Coalgebra

Convenience constructor for a Moore machine packaged as a `Coalgebra`.
Same arguments as [`moore_machine`](@ref) but returns the typed object.

```julia
S = FinPolySet([:s1, :s2])
I = FinPolySet([:lo, :hi])
A = FinPolySet([:tick])
c = moore_machine_coalgebra(S, I, A,
        s -> s == :s1 ? :lo : :hi,
        (s, _a) -> s == :s1 ? :s2 : :s1)
```
"""
function moore_machine_coalgebra(S::PolySet, I::PolySet, A::PolySet,
                                  return_fn::Function, update_fn::Function)
    Coalgebra(moore_machine(S, I, A, return_fn, update_fn))
end

# ============================================================
# CoalgebraMorphism
# ============================================================

"""
    CoalgebraMorphism(dom::Coalgebra, cod::Coalgebra, map::Lens)

A morphism between `polynomial`-coalgebras. `dom` and `cod` must share
the same `polynomial`; `map : Sy^dom.carrier → Sy^cod.carrier` is the
state-space map.

The commuting square checked by [`validate_coalgebra_morphism`](@ref):

    map ⨟ cod.structure  ==  dom.structure

intuitively, "translating states first, then stepping in cod" agrees
with "stepping in dom". The constructor type-checks shape; the law
check is run on demand.
"""
struct CoalgebraMorphism
    dom::Coalgebra
    cod::Coalgebra
    map::Lens
    function CoalgebraMorphism(dom::Coalgebra, cod::Coalgebra, map::Lens)
        dom.polynomial == cod.polynomial ||
            error("CoalgebraMorphism: dom.polynomial ≠ cod.polynomial; " *
                  "coalgebra morphisms are over the same endofunctor")
        map.dom == state_system(dom.carrier) ||
            error("CoalgebraMorphism: map.dom ≠ state_system(dom.carrier)")
        map.cod == state_system(cod.carrier) ||
            error("CoalgebraMorphism: map.cod ≠ state_system(cod.carrier)")
        new(dom, cod, map)
    end
end

function show(io::IO, f::CoalgebraMorphism)
    print(io, "CoalgebraMorphism(dom.carrier=", f.dom.carrier,
          ", cod.carrier=", f.cod.carrier, ")")
end

"""
    validate_coalgebra_morphism(f::CoalgebraMorphism) -> Bool

Check the commuting square `f.map ⨟ f.cod.structure == f.dom.structure`.
Returns `true` iff the square commutes.

For the structured-result form, see [`validate_coalgebra_morphism_detailed`](@ref).
"""
validate_coalgebra_morphism(f::CoalgebraMorphism) =
    validate_coalgebra_morphism_detailed(f).passed

"""
    validate_coalgebra_morphism_detailed(f::CoalgebraMorphism) -> ValidationResult

Same as [`validate_coalgebra_morphism`](@ref), with structural failure
detail.
"""
function validate_coalgebra_morphism_detailed(f::CoalgebraMorphism)
    failures = ValidationFailure[]
    composed = compose(f.map, f.cod.structure)
    if composed != f.dom.structure
        push!(failures, ValidationFailure(
            :commuting_square, (),
            "f.map ⨟ f.cod.structure ≠ f.dom.structure — translating states " *
            "via f.map then stepping in cod doesn't agree with stepping in dom directly",
            composed, f.dom.structure))
    end
    isempty(failures) ? pass("coalgebra morphism (commuting square)") : fail(failures)
end
