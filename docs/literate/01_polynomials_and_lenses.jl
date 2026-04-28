# # Polynomials and lenses
#
# A walking tour of the basic objects in `Poly.jl`. We'll build a polynomial,
# look at its functor action, then build a lens and inspect it.

using Poly

# ## A polynomial by hand
#
# A polynomial functor is determined by a position-set `p(1)` and, for each
# position `i`, a direction-set `p[i]`. The book writes this as
# `p ≅ Σ_{i ∈ p(1)} y^{p[i]}`.

p = Polynomial(FinPolySet([:needy, :greedy, :content]),
               i -> i == :needy   ? FinPolySet([:save, :spend]) :
                    i == :greedy  ? FinPolySet([:accept, :reject, :ask_for_more]) :
                                    FinPolySet([:count, :rest]))

# The default `show` collapses summands by direction-set cardinality —
# book-canonical form:

p

# A more verbose structural display is available via `MIME"text/plain"`,
# which keeps summands distinct when their direction-sets actually differ:

sprint(show, MIME"text/plain"(), p)

# ## The `@poly` macro
#
# For the common case of integer coefficients on `y^k`, the `@poly` macro is
# faster to type:

q = @poly y^4 + y^2 + 1

# ## The functor action
#
# Applying `p` to a set computes `p(X) = Σ_{i ∈ p(1)} X^{p[i]}`. For finite
# inputs Poly.jl enumerates the `(i, g)` pairs explicitly.

X = FinPolySet([:a, :b])
pX = p(X)
cardinality(pX)

# Or just the cardinality, computed symbolically without enumeration:

cardinality_of_apply(p, X)

# ## A lens
#
# A lens `f : p → q` is a pair `(f₁, f♯)`: a forward function on positions
# and, for each position `i`, a *backward* function from `q[f₁(i)]` to `p[i]`
# on directions. The classic interaction example is the coin-jar / owner
# protocol:

coin_jar = Polynomial(FinPolySet([:open, :closed]),
                      i -> i == :open ? FinPolySet([:penny, :nickel, :dime, :quarter]) :
                                         FinPolySet(Symbol[]))

interaction = Lens(p, coin_jar,
                   i -> (i == :content) ? :closed : :open,
                   (i, b) -> begin
                       if i == :needy
                           b == :penny ? :spend : :save
                       elseif i == :greedy
                           (b == :penny || b == :nickel) ? :ask_for_more : :accept
                       else
                           error("vacuous: q[closed] has no directions")
                       end
                   end)

# ## The polybox picture
#
# A lens is presented in the book as a "polybox": `f₁` flowing forward across
# the top, `f♯` flowing backward across the bottom. `polybox` renders this as
# ASCII; pass `entries=(i, b)` to populate a specific cell.

println(polybox(interaction; entries=(:greedy, :dime)))

# ## How many lenses are there?
#
# `lens_count(p, q)` computes `|Poly(p, q)| = Π_{i ∈ p(1)} |q(p[i])|` without
# enumerating all of them.

lens_count(p, coin_jar)

# ## Identity and composition
#
# `identity_lens(p)` is the identity, and `compose(f, g)` (or `f ⨟ g`) is
# vertical composition.

id_p = identity_lens(p)
@assert compose(id_p, interaction) == interaction
