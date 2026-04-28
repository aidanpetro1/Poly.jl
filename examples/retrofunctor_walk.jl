"""
    examples/retrofunctor_walk.jl

A worked retrofunctor between two non-trivial comonoids. Demonstrates
Sprint 7's `Comonoid` / `Retrofunctor` / `validate_retrofunctor`.

We build:
- A *coarse* comonoid `Coarse` on three states {:up, :down, :flat} —
  the contractible groupoid (every pair has a unique iso between them).
- A *fine* comonoid `Fine` on six states arranged in two parallel worlds:
  the `_a` world {:rising_a, :falling_a, :level_a} and the `_b` world
  {:rising_b, :falling_b, :level_b}. Each world is itself a contractible
  groupoid; the two worlds don't interact.

The retrofunctor `F : Fine → Coarse` projects each world onto Coarse by
forgetting the suffix. The key constraint: for `F` to satisfy the comonoid
morphism laws (counit + comult), the *direction-side* lift must respect
the suffix — i.e., starting from `:rising_a` and asking "what's the target
state for phase :down?" we must answer `:falling_a` (same world), not
`:falling_b`. Otherwise the counit law `F♯_s(phase(s)) = s` fails for
`_b` states.

Run with:
    julia --project=. examples/retrofunctor_walk.jl
"""

include(joinpath(@__DIR__, "..", "src", "Poly.jl"))
using .Poly

# Coarse comonoid: 3 abstract phases.
const Coarse = state_system_comonoid(FinPolySet([:up, :down, :flat]))

# Fine comonoid: 6 concrete states, two per phase.
const Fine = state_system_comonoid(
    FinPolySet([:rising_a, :rising_b, :falling_a, :falling_b, :level_a, :level_b])
)

# The "phase" of each fine state.
const phase = Dict(
    :rising_a  => :up,    :rising_b  => :up,
    :falling_a => :down,  :falling_b => :down,
    :level_a   => :flat,  :level_b   => :flat,
)

# The "side" / parallel-world tag of each fine state.
const side = Dict(
    :rising_a  => :a, :rising_b  => :b,
    :falling_a => :a, :falling_b => :b,
    :level_a   => :a, :level_b   => :b,
)

# Build the lift table: (target phase, source side) → target fine state.
# This is the data that lets the retrofunctor satisfy both counit (which
# forces F♯_s(phase(s)) = s) and comult (which forces the lift to compose
# functorially).
const _lift = Dict(
    (:up,   :a) => :rising_a,  (:up,   :b) => :rising_b,
    (:down, :a) => :falling_a, (:down, :b) => :falling_b,
    (:flat, :a) => :level_a,   (:flat, :b) => :level_b,
)

const F = Retrofunctor(
    Fine, Coarse,
    Lens(
        Fine.carrier, Coarse.carrier,
        s -> phase[s],
        (s, target_phase) -> _lift[(target_phase, side[s])],
    ),
)

function demo()
    println("Coarse comonoid: ", Coarse)
    println("Fine comonoid:   ", Fine)

    println()
    println("Phase map (on positions):")
    for s in Fine.carrier.positions.elements
        println("  $s ↦ $(F.underlying.on_positions.f(s))")
    end

    println()
    println("Lifted morphisms (on directions):")
    for s in Fine.carrier.positions.elements
        for q in Coarse.carrier.positions.elements
            lifted = F.underlying.on_directions.f(s).f(q)
            println("  at $s, target phase $q → fine target $lifted")
        end
    end

    println()
    println("Validate retrofunctor (strict): ", validate_retrofunctor(F))
    @assert validate_retrofunctor(F)
    println("  ✓ both counit and comult preservation hold")

    # Convert both ends to SmallCategory to make the morphism structure visible.
    println()
    Cc = to_category(Coarse)
    Cf = to_category(Fine)
    println("Coarse as a category: ", Cc)
    println("Fine   as a category: ", Cf)
    println()
    println("Number of Fine morphisms preserving each side: ",
            count(m -> side[m[1]] == side[Cf.cod[m]], Cf.morphisms.elements),
            " / ", cardinality(Cf.morphisms))
end

if abspath(PROGRAM_FILE) == @__FILE__
    demo()
end
