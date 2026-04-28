"""
    examples/moore_machine_simulation.jl

A small worked example: build a Moore machine on three states, run it on an
input sequence, and inspect the trajectory + outputs. Demonstrates Sprint 6.

The machine recognizes the pattern "two consecutive `:tick` inputs followed
by a `:reset`". It has three states:
- `:idle`     — no recent ticks
- `:one`      — one tick seen
- `:matched`  — pattern matched (output 1)

Run with:
    julia --project=. examples/moore_machine_simulation.jl
"""

include(joinpath(@__DIR__, "..", "src", "Poly.jl"))
using .Poly

# State set, input set, output set.
const S = FinPolySet([:idle, :one, :matched])
const A = FinPolySet([:tick, :reset])
const I = FinPolySet([0, 1])

# Output: 1 only at :matched, 0 otherwise.
return_fn = s -> s == :matched ? 1 : 0

# Transition: counts ticks; :reset always returns to :idle.
update_fn = (s, a) -> begin
    if a == :reset
        :idle
    elseif a == :tick
        s == :idle ? :one :
        s == :one  ? :matched :
                     :matched   # already matched, stays
    else
        error("unknown input: $a")
    end
end

const φ = moore_machine(S, I, A, return_fn, update_fn)

function demo()
    println("Moore machine: pattern detector for two consecutive ticks.")
    println("  States: ", S)
    println("  Inputs: ", A)
    println("  Outputs: ", I)
    println()

    inputs = [:tick, :reset, :tick, :tick, :reset, :tick, :tick, :tick]
    println("Input sequence: ", inputs)

    states = trajectory(φ, :idle, inputs)
    outs   = output_trajectory(φ, :idle, inputs)
    println()
    println("State trajectory:    ", states)
    println("Output trajectory:   ", outs)

    # Sanity-check: output sequence has 1 at exactly the indices where two
    # consecutive ticks have just been seen.
    @assert outs == [0, 0, 0, 0, 1, 0, 0, 1, 1]
    println()
    println("Pattern fires exactly when expected. ✓")

    # Step-by-step: just demonstrate `step`.
    println()
    println("step(φ, :idle, :tick) = ", step(φ, :idle, :tick))
    println("step(φ, :one,  :tick) = ", step(φ, :one, :tick))
    println("step(φ, :matched, :reset) = ", step(φ, :matched, :reset))
end

if abspath(PROGRAM_FILE) == @__FILE__
    demo()
end
