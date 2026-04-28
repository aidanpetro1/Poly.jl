# ============================================================
# PolySet hierarchy
# ============================================================

"""
    PolySet

The kinds of sets that show up as positions or directions of a polynomial.
Every concrete subtype must support [`cardinality`](@ref). Finite, enumerable
subtypes additionally support iteration (`iterate`, `length`, `eltype`, `in`).
Symbolic subtypes carry only metadata.
"""
abstract type PolySet end

"""
    FinPolySet(elements)

A finite enumerable set, backed by a `Vector` of its elements.
Duplicates are removed during construction.
"""
struct FinPolySet{T} <: PolySet
    elements::Vector{T}
    function FinPolySet(elts::AbstractVector{T}) where {T}
        new{T}(unique(elts))
    end
end
FinPolySet(elts...) = FinPolySet(collect(elts))

"""
    cardinality(s::PolySet) -> Cardinality

The cardinality of a `PolySet`, computed in the cardinality algebra. Each
`PolySet` subtype implements this directly:

- `FinPolySet`: `Finite(length(elements))`.
- `NatSet`, `IntSet`: `CountablyInfinite()`.
- `RealSet`, `IntervalSet`: `Continuum()`.
- `ProductSet(a, b)`, `SumSet(a, b)`, `ExpSet(a, b)`: derived as
  `cardinality(a) * cardinality(b)`, `cardinality(a) + cardinality(b)`,
  `cardinality(b) ^ cardinality(a)` respectively.
- `SymbolicSet(name)`: `SymbolicCardinality(name)`.
"""
cardinality(s::FinPolySet) = Finite(length(s.elements))
length(s::FinPolySet) = length(s.elements)
eltype(::FinPolySet{T}) where {T} = T
iterate(s::FinPolySet, st=1) = st > length(s.elements) ? nothing : (s.elements[st], st + 1)
in(x, s::FinPolySet) = x in s.elements
==(a::FinPolySet, b::FinPolySet) = Set(a.elements) == Set(b.elements)
hash(s::FinPolySet, h::UInt) = hash((:FinPolySet, Set(s.elements)), h)

"The set of natural numbers ℕ = {0, 1, 2, ...}."
struct NatSet <: PolySet end
cardinality(::NatSet) = CountablyInfinite()
eltype(::NatSet) = Int

"The set of integers ℤ."
struct IntSet <: PolySet end
cardinality(::IntSet) = CountablyInfinite()
eltype(::IntSet) = Int

"The set of real numbers ℝ."
struct RealSet <: PolySet end
cardinality(::RealSet) = Continuum()
eltype(::RealSet) = Float64

==(::NatSet, ::NatSet) = true
==(::IntSet, ::IntSet) = true
==(::RealSet, ::RealSet) = true
hash(::NatSet, h::UInt) = hash(:NatSet, h)
hash(::IntSet, h::UInt) = hash(:IntSet, h)
hash(::RealSet, h::UInt) = hash(:RealSet, h)

"""
    IntervalSet(lo, hi; lo_open=false, hi_open=false)

A real interval `[lo, hi]` (with optional open endpoints). Used to model the
intervals in dynamical-systems examples like `[0, 20]`, `(0, ∞)`, etc.
"""
struct IntervalSet{T<:Real} <: PolySet
    lo::T
    hi::T
    lo_open::Bool
    hi_open::Bool
    IntervalSet(lo::T, hi::T; lo_open=false, hi_open=false) where {T<:Real} =
        new{T}(lo, hi, lo_open, hi_open)
end
cardinality(::IntervalSet) = Continuum()
eltype(::IntervalSet{T}) where {T} = T
function in(x::Real, s::IntervalSet)
    lo_ok = s.lo_open ? x > s.lo : x ≥ s.lo
    hi_ok = s.hi_open ? x < s.hi : x ≤ s.hi
    lo_ok && hi_ok
end
==(a::IntervalSet, b::IntervalSet) = a.lo == b.lo && a.hi == b.hi && a.lo_open == b.lo_open && a.hi_open == b.hi_open
hash(s::IntervalSet, h::UInt) = hash((:IntervalSet, s.lo, s.hi, s.lo_open, s.hi_open), h)

"""
    ProductSet(factors...)

The cartesian product of `PolySet`s. Elements are tuples.
"""
struct ProductSet{T<:Tuple} <: PolySet
    factors::T
    ProductSet(factors::PolySet...) = new{typeof(factors)}(factors)
end
cardinality(s::ProductSet) = reduce(*, cardinality.(s.factors); init=Finite(1))
==(a::ProductSet, b::ProductSet) = a.factors == b.factors
hash(s::ProductSet, h::UInt) = hash((:ProductSet, s.factors), h)

function iterate(s::ProductSet)
    !all(f -> f isa FinPolySet, s.factors) && error("ProductSet iteration requires all FinPolySet factors")
    iters = Iterators.product((f.elements for f in s.factors)...)
    state = iterate(iters)
    state === nothing && return nothing
    return (state[1], (iters, state[2]))
end
function iterate(::ProductSet, st)
    (iters, inner) = st
    state = iterate(iters, inner)
    state === nothing && return nothing
    return (state[1], (iters, state[2]))
end

"""
    SumSet(summands...)

Disjoint union of `PolySet`s.
"""
struct SumSet{T<:Tuple} <: PolySet
    summands::T
    SumSet(summands::PolySet...) = new{typeof(summands)}(summands)
end
cardinality(s::SumSet) = reduce(+, cardinality.(s.summands); init=Finite(0))
==(a::SumSet, b::SumSet) = a.summands == b.summands
hash(s::SumSet, h::UInt) = hash((:SumSet, s.summands), h)

"""
    ExpSet(base, exp)

The set of functions from `exp` to `base`, written `base ^ exp` mathematically.
Cardinality `|base|^|exp|`.
"""
struct ExpSet <: PolySet
    base::PolySet
    exp::PolySet
end
cardinality(s::ExpSet) = cardinality(s.base) ^ cardinality(s.exp)
==(a::ExpSet, b::ExpSet) = a.base == b.base && a.exp == b.exp
hash(s::ExpSet, h::UInt) = hash((:ExpSet, s.base, s.exp), h)

"""
    SymbolicSet(name; cardinality=nothing)

An opaque set referred to by name only. Optionally carries a [`Cardinality`](@ref).
"""
struct SymbolicSet <: PolySet
    name::Symbol
    cardinality::Union{Cardinality,Nothing}
    SymbolicSet(name::Symbol; cardinality=nothing) = new(name, cardinality)
end
cardinality(s::SymbolicSet) =
    s.cardinality === nothing ? SymbolicCardinality(s.name) : s.cardinality
==(a::SymbolicSet, b::SymbolicSet) = a.name == b.name
hash(s::SymbolicSet, h::UInt) = hash((:SymbolicSet, s.name), h)

# Display
show(io::IO, s::FinPolySet) = print(io, "{", join(repr.(s.elements), ", "), "}")
show(io::IO, ::NatSet) = print(io, "ℕ")
show(io::IO, ::IntSet) = print(io, "ℤ")
show(io::IO, ::RealSet) = print(io, "ℝ")
function show(io::IO, s::IntervalSet)
    print(io, s.lo_open ? "(" : "[", s.lo, ", ", s.hi, s.hi_open ? ")" : "]")
end
show(io::IO, s::ProductSet) = print(io, "(", join(sprint.(show, s.factors), " × "), ")")
show(io::IO, s::SumSet) = print(io, "(", join(sprint.(show, s.summands), " + "), ")")
show(io::IO, s::ExpSet) = (print(io, "("); show(io, s.base); print(io, ")^("); show(io, s.exp); print(io, ")"))
show(io::IO, s::SymbolicSet) = print(io, s.name)
