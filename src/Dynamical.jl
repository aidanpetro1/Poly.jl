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
