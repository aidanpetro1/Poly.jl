"""
    examples/coin_jar_owner.jl

A worked example based on Niu & Spivak Examples 2.19 and 3.10: modeling the
interaction between a coin jar and its owner as a lens between polynomials.

The coin jar `q` has two positions, open and closed. When open, it can accept
any of four coin denominations (its directions); when closed, it accepts none.
The owner `p` has three moods (needy, greedy, content), each with its own list
of available actions.

A lens `f : p → q` then encodes a particular interaction protocol: how each of
the owner's moods determines whether the jar is open or closed, and how the
coin received (when the jar is open) determines the owner's chosen action.
"""

include(joinpath(@__DIR__, "..", "src", "Poly.jl"))
using .Poly

# Coin jar
const coin_jar = Polynomial(
    FinPolySet([:open, :closed]),
    i -> i == :open  ? FinPolySet([:penny, :nickel, :dime, :quarter]) :
                       FinPolySet(Symbol[])
)

# Owner
const owner = Polynomial(
    FinPolySet([:needy, :greedy, :content]),
    i -> i == :needy   ? FinPolySet([:save, :spend]) :
         i == :greedy  ? FinPolySet([:accept, :reject, :ask_for_more]) :
                         FinPolySet([:count, :rest])
)

# Interaction lens
const interaction = Lens(
    owner, coin_jar,
    i -> (i == :content) ? :closed : :open,
    (i, b) -> begin
        if i == :needy
            b == :penny ? :spend : :save
        elseif i == :greedy
            (b == :penny || b == :nickel) ? :ask_for_more : :accept
        else
            error("vacuous: q[closed] has no directions")
        end
    end
)

# A small demo
function demo()
    println("Coin jar:    ", coin_jar)
    println("Owner:       ", owner)
    println("Interaction: ", interaction)
    println()
    println("Polybox at (mood=:greedy, coin=:dime):")
    print(polybox(interaction; entries=(:greedy, :dime)))
    println()
    println("Number of distinct interaction lenses owner → coin_jar: ",
            lens_count(owner, coin_jar))
end

if abspath(PROGRAM_FILE) == @__FILE__
    demo()
end
