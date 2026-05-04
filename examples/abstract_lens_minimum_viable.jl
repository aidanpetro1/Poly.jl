"""
    examples/abstract_lens_minimum_viable.jl

# AbstractLens — minimum viable subtype

Demonstrates the v0.6 `AbstractLens` five-function contract by
implementing a trivial `IdentityLensWrapper` that wraps a `Polynomial`
and acts as its identity lens.

Authored as a `.jl` script to match the rest of `examples/`. Each
section can be copy-pasted into a Pluto cell; the file also runs end-
to-end from the command line:

    julia --project=. examples/abstract_lens_minimum_viable.jl

Cross-reference: `docs/dev/abstract_lens.md` (the extension contract).
"""

include(joinpath(@__DIR__, "..", "src", "Poly.jl"))
using .Poly

# ============================================================
# Define a minimum viable AbstractLens subtype
# ============================================================

struct IdentityLensWrapper <: AbstractLens
    p::Polynomial
end

# Implement the five-function interface. Each method is qualified
# with the `Poly.` prefix because the names are exported from `Poly`
# and we're declaring NEW methods on those generic functions.

Poly.dom(L::IdentityLensWrapper) = L.p
Poly.cod(L::IdentityLensWrapper) = L.p

Poly.on_positions(L::IdentityLensWrapper) =
    PolyFunction(positions(L.p), positions(L.p), identity)

Poly.on_directions(L::IdentityLensWrapper) = DependentFunction(
    positions(L.p),
    i -> ExpSet(direction_at(L.p, i), direction_at(L.p, i)),
    i -> PolyFunction(direction_at(L.p, i), direction_at(L.p, i), identity)
)

Poly.is_deterministic(::IdentityLensWrapper) = true

# ============================================================
# Exercise the contract
# ============================================================

p = Polynomial(FinPolySet([1, 2]), i -> FinPolySet([:a]))   # 2y
L = IdentityLensWrapper(p)

@assert L isa AbstractLens
@assert !(L isa Lens)                  # peer type, not a Lens
@assert dom(L) === p
@assert cod(L) === p
@assert on_positions(L) isa PolyFunction
@assert on_directions(L) isa DependentFunction
@assert is_deterministic(L) === true

println("IdentityLensWrapper passes the AbstractLens contract:")
println("  dom(L)              = ", dom(L))
println("  cod(L)              = ", cod(L))
println("  on_positions(L)     = ", on_positions(L))
println("  on_directions(L)    = ", on_directions(L))
println("  is_deterministic(L) = ", is_deterministic(L))

# ============================================================
# What this subtype does NOT inherit
# ============================================================
#
# `compose(::IdentityLensWrapper, ::IdentityLensWrapper)` is undefined
# — no method exists. This establishes the "no free arithmetic" point:
# the abstract supertype gives signature compatibility for the
# interface methods only. Subtypes that want to participate in
# monoidal / substitution / vertical operations must define those
# methods on their own type.

let caught = false
    try
        compose(L, L)
    catch e
        caught = e isa MethodError
        println()
        println("Expected MethodError on `compose(L, L)`:")
        println("  ", e)
    end
    @assert caught "compose(::IdentityLensWrapper, ::IdentityLensWrapper) should not exist"
end
