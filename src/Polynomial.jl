# ============================================================
# Polynomial
# ============================================================

"""
    Polynomial(positions, direction_at)

A polynomial functor `p : Set → Set` represented by its position-set
`p(1) = positions` together with the indexed family of direction-sets
`p[i] = direction_at(i)` for each `i ∈ p(1)`. Mathematically,

    p ≅ Σ_{i ∈ p(1)} y^{p[i]}

following Niu & Spivak Definition 2.1 / Proposition 2.6.

`direction_at` is a `DependentFunction` whose body returns a `PolySet` for
each position. Use [`indexed_family`](@ref) when you have just a callable.
"""
struct Polynomial
    positions::PolySet
    direction_at::DependentFunction
    function Polynomial(pos::PolySet, dat::DependentFunction)
        dat.dom == pos || error("direction_at domain $(dat.dom) ≠ positions $pos")
        new(pos, dat)
    end
end

"""
    Polynomial(positions, dir_at_fn::Function)

Convenience constructor. `dir_at_fn` is a plain callable `i ↦ PolySet`.
"""
Polynomial(pos::PolySet, dir_at_fn::Function) =
    Polynomial(pos, indexed_family(pos, dir_at_fn))

"`p(1)` — the set of positions of `p`."
positions(p::Polynomial) = p.positions

"`p[i]` — the direction-set of `p` at position `i`."
direction_at(p::Polynomial, i) = p.direction_at(i)

# Special polynomials -------------------------------------------------

"The identity polynomial functor `y ≅ y¹`. One position, one direction."
const y = Polynomial(FinPolySet([:pt]), _ -> FinPolySet([:pt]))

"The constant polynomial `0`. No positions, no directions. Initial in **Poly**."
const zero_poly = Polynomial(FinPolySet(Symbol[]), i -> FinPolySet(Symbol[]))

"The constant polynomial `1 ≅ y⁰`. One position, no directions. Terminal in **Poly**."
const one_poly = Polynomial(FinPolySet([:pt]), _ -> FinPolySet(Symbol[]))

"The constant polynomial `I ≅ Σ_{i ∈ I} y⁰`. Each position has zero directions."
constant(I::PolySet) = Polynomial(I, _ -> FinPolySet(Symbol[]))

"The linear polynomial `Iy`. Each position has exactly one direction."
linear(I::PolySet) = Polynomial(I, _ -> FinPolySet([:pt]))

"The monomial polynomial `Iy^A`. Every position has direction-set `A`."
monomial(I::PolySet, A::PolySet) = Polynomial(I, _ -> A)

"The representable polynomial `y^A`. One position, direction-set `A`."
representable(A::PolySet) = Polynomial(FinPolySet([:pt]), _ -> A)

# Predicates ---------------------------------------------------------

function _all_directions_empty(p::Polynomial)
    pos = p.positions
    pos isa FinPolySet || return false
    all(i -> cardinality(direction_at(p, i)) == Finite(0), pos)
end

function _all_directions_singleton(p::Polynomial)
    pos = p.positions
    pos isa FinPolySet || return false
    all(i -> cardinality(direction_at(p, i)) == Finite(1), pos)
end

function _all_directions_equal(p::Polynomial)
    pos = p.positions
    pos isa FinPolySet || return false
    isempty(pos.elements) && return true
    a = direction_at(p, first(pos))
    all(i -> direction_at(p, i) == a, pos)
end

"True iff every direction-set of `p` is empty (`p ≅ I` for some set `I`)."
is_constant(p::Polynomial) = _all_directions_empty(p)

"True iff every direction-set of `p` is a singleton (`p ≅ Iy` for some `I`)."
is_linear(p::Polynomial) = _all_directions_singleton(p)

"True iff `p(1) ≅ 1` (one position; `p ≅ y^A` for some `A`)."
is_representable(p::Polynomial) = cardinality(p.positions) == Finite(1)

"True iff every direction-set of `p` has the same cardinality (`p ≅ Iy^A`)."
is_monomial(p::Polynomial) = _all_directions_equal(p)

# Equality and hashing -----------------------------------------------

"""
    ==(p::Polynomial, q::Polynomial)

Strict structural equality: `p.positions == q.positions` AND, for every
`i ∈ p(1)`, `direction_at(p, i) == direction_at(q, i)`.

For the up-to-iso predicate, see [`is_iso`](@ref) and [`is_iso_strict`](@ref).
Errors when position-sets are non-finite (we can't iterate to check).
"""
function ==(p::Polynomial, q::Polynomial)
    p.positions == q.positions || return false
    pos = p.positions
    if pos isa FinPolySet
        return all(i -> direction_at(p, i) == direction_at(q, i), pos)
    end
    error("Polynomial == is undecidable for non-finite position-sets; got $(typeof(pos)).")
end

function hash(p::Polynomial, h::UInt)
    pos = p.positions
    if pos isa FinPolySet
        h = hash(:Polynomial, h)
        h = hash(pos, h)
        for i in pos
            h = hash(direction_at(p, i), h)
        end
        return h
    end
    hash((:Polynomial, pos), h)
end

# Isomorphism predicates ---------------------------------------------

"""
    is_iso(p::Polynomial, q::Polynomial) -> Bool

True iff `p` and `q` are isomorphic *up to direction-set cardinality*: their
position-sets have equal cardinality, and for each cardinality `c`, both have
the same number of positions whose direction-set has cardinality `c`.

For the stricter version that distinguishes direction-sets that happen to
share a cardinality, see [`is_iso_strict`](@ref).

# `==` vs `is_iso`
- `p == q`: strict structural equality. Same position-set, same direction-set
  per position (compared via PolySet `==`). Differs from `is_iso` in that
  it requires the positions to be the *same elements*, not just isomorphic.
  After Sprint 3 monoidal products: `p × q != q × p` (positions differ in
  tuple order) but `is_iso(p × q, q × p) == true`.
- `is_iso(p, q)`: cardinality-iso. Matches the book's "polynomials live up to
  iso" convention.
- `is_iso_strict(p, q)`: structural iso. Bijection of positions matching
  direction-sets exactly.
- `p ≈ q`: Unicode alias for `is_iso(p, q)`.
"""
function is_iso(p::Polynomial, q::Polynomial)
    cardinality(p.positions) == cardinality(q.positions) || return false
    (p.positions isa FinPolySet && q.positions isa FinPolySet) ||
        error("is_iso requires finite position-sets")
    pms = Dict{Cardinality,Int}()
    for i in p.positions
        c = cardinality(direction_at(p, i))
        pms[c] = get(pms, c, 0) + 1
    end
    qms = Dict{Cardinality,Int}()
    for i in q.positions
        c = cardinality(direction_at(q, i))
        qms[c] = get(qms, c, 0) + 1
    end
    pms == qms
end

"""
    is_iso_strict(p::Polynomial, q::Polynomial) -> Bool

True iff there is a bijection `π : p.positions → q.positions` such that
`direction_at(p, i) == direction_at(q, π(i))` for every `i ∈ p(1)`.
Stricter than [`is_iso`](@ref): distinguishes ℕy from ℝy etc.
"""
function is_iso_strict(p::Polynomial, q::Polynomial)
    cardinality(p.positions) == cardinality(q.positions) || return false
    (p.positions isa FinPolySet && q.positions isa FinPolySet) ||
        error("is_iso_strict requires finite position-sets")
    pms = Dict{PolySet,Int}()
    for i in p.positions
        d = direction_at(p, i)
        pms[d] = get(pms, d, 0) + 1
    end
    qms = Dict{PolySet,Int}()
    for i in q.positions
        d = direction_at(q, i)
        qms[d] = get(qms, d, 0) + 1
    end
    pms == qms
end

"""
    p ≈ q

Unicode alias for [`is_iso`](@ref). The natural operator for "these are
isomorphic" comparisons in book-style identities like `p ⊗ y ≈ p`,
`p × q ≈ q × p`, etc.

To get the stricter direction-set-aware iso, use `is_iso_strict(p, q)` directly.
"""
Base.:≈(p::Polynomial, q::Polynomial) = is_iso(p, q)

# Functor action p(X) ------------------------------------------------

"""
    apply(p::Polynomial, X::PolySet) -> PolySet

The functor action `p(X) = Σ_{i ∈ p(1)} X^{p[i]}` (Niu & Spivak Proposition 2.10).

For finite `p(1)` and finite `X` (with all direction-sets finite), this
enumerates `(i, g)` pairs where `g : p[i] → X`. Otherwise returns a
`SumSet`/`SymbolicSet` carrier.
"""
function apply(p::Polynomial, X::PolySet)
    cp = cardinality(p.positions)
    if cp isa Finite && p.positions isa FinPolySet
        if X isa FinPolySet && all(i -> direction_at(p, i) isa FinPolySet, p.positions)
            elements = Tuple[]
            for i in p.positions
                Di = direction_at(p, i)::FinPolySet
                if isempty(Di.elements)
                    push!(elements, (i, Dict{eltype(Di),eltype(X)}()))
                else
                    for tup in Iterators.product((X.elements for _ in Di.elements)...)
                        g = Dict(zip(Di.elements, tup))
                        push!(elements, (i, g))
                    end
                end
            end
            return FinPolySet(elements)
        else
            return SumSet((ExpSet(X, direction_at(p, i)) for i in p.positions)...)
        end
    end
    SymbolicSet(Symbol("p(", X, ")"))
end

# Make Polynomial callable.
(p::Polynomial)(X::PolySet) = apply(p, X)

"""
    cardinality_of_apply(p::Polynomial, X::PolySet) -> Cardinality

The cardinality of `p(X)` computed *symbolically* via the cardinality algebra,
without enumeration:

    |p(X)| = Σ_{i ∈ p(1)} |X|^|p[i]|

Works for any combination of finite, infinite, or symbolic position-sets and
direction-sets, and is the right tool for hom-set sizing (`lens_count`) when
enumerating `p(X)` would be wasteful or impossible.
"""
function cardinality_of_apply(p::Polynomial, X::PolySet)
    cX = cardinality(X)
    pos = p.positions
    if pos isa FinPolySet
        isempty(pos.elements) && return Finite(0)
        return reduce(+, (cX ^ cardinality(direction_at(p, i)) for i in pos))
    end
    SymbolicCardinality(Symbol("|", sprint(show, p), "(", sprint(show, X), ")|"))
end

# ============================================================
# Display: merged book form (default) + structural form (MIME)
# ============================================================

"""
Internal: group summands by direction-set cardinality alone — the book-style
canonical display where `y^3 + y^2 + y^2` becomes `y^3 + 2y^2`.
"""
function _summarize_polynomial_merged(p::Polynomial)
    p.positions isa FinPolySet || return nothing
    isempty(p.positions.elements) && return Tuple{Int,Cardinality}[]

    seen = Dict{Cardinality,Int}()
    for i in p.positions
        cd = cardinality(direction_at(p, i))
        seen[cd] = get(seen, cd, 0) + 1
    end
    summands = [(n, cd) for (cd, n) in seen]
    sort!(summands; by = t -> begin
        cd = t[2]
        cd isa Finite ? (-1, -cd.n) : (0, _card_key(cd))
    end)
    summands
end

"""
Internal: keep summands distinct when direction-sets differ at equal
cardinality. Used by the structural / verbose display.
"""
function _summarize_polynomial_structural(p::Polynomial)
    p.positions isa FinPolySet || return nothing
    isempty(p.positions.elements) && return Tuple{Int,Cardinality,String}[]

    seen = Dict{Tuple{Cardinality,String},Int}()
    for i in p.positions
        Di = direction_at(p, i)
        key = (cardinality(Di), sprint(show, Di))
        seen[key] = get(seen, key, 0) + 1
    end
    summands = [(n, cd, rep) for ((cd, rep), n) in seen]
    sort!(summands; by = t -> begin
        cd = t[2]
        cd isa Finite ? (-1, -cd.n, t[3]) : (0, 0, t[3])
    end)
    summands
end

# Render one (coef, cardinality, optional label) summand.
function _render_summand(io::IO, n::Int, cd::Cardinality, label=nothing)
    coef = n == 1 ? "" : string(n)
    if cd == Finite(0)
        print(io, n == 1 ? "1" : string(n))
    elseif cd == Finite(1)
        print(io, coef, "y")
    elseif cd isa Finite
        print(io, coef, "y^", cd.n)
    else
        exp = label === nothing ? sprint(show, cd) : label
        print(io, coef, "y^", exp)
    end
end

"""
    show(io::IO, p::Polynomial)

Compact, book-canonical display: summands merged by direction-set cardinality.
"""
function show(io::IO, p::Polynomial)
    s = _summarize_polynomial_merged(p)
    if s === nothing
        print(io, "Polynomial(positions=")
        show(io, p.positions)
        print(io, ")")
        return
    end
    if isempty(s)
        print(io, "0")
        return
    end
    first_part = true
    for (n, cd) in s
        first_part || print(io, " + ")
        _render_summand(io, n, cd)
        first_part = false
    end
end

"""
    show(io::IO, ::MIME"text/plain", p::Polynomial)

Verbose structural display: summands distinct when direction-sets differ.
This is what the REPL invokes when you display `p` directly.
"""
function show(io::IO, ::MIME"text/plain", p::Polynomial)
    s = _summarize_polynomial_structural(p)
    if s === nothing
        print(io, "Polynomial(positions=")
        show(io, p.positions)
        print(io, ")")
        return
    end
    if isempty(s)
        print(io, "0")
        return
    end
    first_part = true
    for (n, cd, rep) in s
        first_part || print(io, " + ")
        _render_summand(io, n, cd, rep)
        first_part = false
    end
end

# ============================================================
# Corolla-forest ASCII renderer
# ============================================================

"""
    corolla_forest(p::Polynomial; max_arrows=8) -> String

Render `p` as an ASCII corolla forest — one corolla per position, with one
upward edge per direction. The book draws these as

```
 ↑ ↑      ↑          •
  •       •          •
```

where `•` is the position (root) and `↑` is a direction (leaf). Constants
(empty direction-sets) appear as bare roots. Direction-sets larger than
`max_arrows` show `↑·n` as a short-hand. Symbolic direction-sets show
`↑·|name|`.
"""
function corolla_forest(p::Polynomial; max_arrows::Int=8)
    pos = p.positions
    if !(pos isa FinPolySet)
        return "⟨corolla forest of " * sprint(show, p) * "⟩"
    end
    isempty(pos.elements) && return "(empty forest)"

    # Build a column for each position. Column has two lines:
    #   line 1: arrow row (↑ ↑ ↑ ...) or "·k" abbreviation, or symbolic label
    #   line 2: the root "•"
    cols = Tuple{String,String}[]
    for i in pos
        Di = direction_at(p, i)
        cd = cardinality(Di)
        if cd == Finite(0)
            push!(cols, ("", "•"))
        elseif cd isa Finite && cd.n ≤ max_arrows
            push!(cols, (join(fill("↑", cd.n), " "), "•"))
        elseif cd isa Finite
            push!(cols, ("↑·" * string(cd.n), "•"))
        else
            push!(cols, ("↑·" * sprint(show, cd), "•"))
        end
    end

    # Center each column to the wider of its two lines.
    line1_parts = String[]
    line2_parts = String[]
    for (top, bot) in cols
        w = max(textwidth(top), textwidth(bot))
        push!(line1_parts, _center(top, w))
        push!(line2_parts, _center(bot, w))
    end
    line1 = join(line1_parts, "    ")
    line2 = join(line2_parts, "    ")
    return line1 * "\n" * line2
end

function _center(s::AbstractString, w::Int)
    pad = w - textwidth(s)
    pad ≤ 0 && return s
    left = pad ÷ 2
    right = pad - left
    return repeat(" ", left) * s * repeat(" ", right)
end
