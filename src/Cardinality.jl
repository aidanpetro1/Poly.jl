# ============================================================
# Cardinality
# ============================================================

"""
    Cardinality

Symbolic algebra of set sizes. Subtypes: [`Finite`](@ref),
[`CountablyInfinite`](@ref), [`Continuum`](@ref), [`SymbolicCardinality`](@ref).

Operations `+`, `*`, `^` are defined among cardinalities so that things like
`|p[i]| ^ |q[j]|` can be tracked symbolically without enumeration.
"""
abstract type Cardinality end

"""
    Finite(n::Int)

A cardinality of exactly `n` elements (`n ≥ 0`).
"""
struct Finite <: Cardinality
    n::Int
    function Finite(n::Integer)
        n < 0 && throw(ArgumentError("Finite cardinality must be ≥ 0, got $n"))
        new(Int(n))
    end
end

"A countably infinite cardinality (ℵ₀)."
struct CountablyInfinite <: Cardinality end

"The cardinality of the continuum."
struct Continuum <: Cardinality end

"""
    SymbolicCardinality(name)

An opaque cardinality referred to by name only (e.g. `|S|`).
"""
struct SymbolicCardinality <: Cardinality
    name::Symbol
end

# Equality and hashing for the leaf cardinalities.
==(a::Finite, b::Finite) = a.n == b.n
==(::CountablyInfinite, ::CountablyInfinite) = true
==(::Continuum, ::Continuum) = true
==(a::SymbolicCardinality, b::SymbolicCardinality) = a.name == b.name
==(a::Cardinality, b::Cardinality) = false
hash(c::Finite, h::UInt) = hash((:Finite, c.n), h)
hash(::CountablyInfinite, h::UInt) = hash(:CountablyInfinite, h)
hash(::Continuum, h::UInt) = hash(:Continuum, h)
hash(c::SymbolicCardinality, h::UInt) = hash((:Symbolic, c.name), h)

"""
A deferred cardinality expression. Built by the symbolic-arithmetic fallback
when at least one operand is a `SymbolicCardinality` or another expression.
Carries an op (`:+`, `:*`, `:^`) and its two arguments.
"""
struct CardinalityExpr <: Cardinality
    op::Symbol
    args::Tuple{Cardinality,Cardinality}
end
==(a::CardinalityExpr, b::CardinalityExpr) = a.op == b.op && a.args == b.args
hash(e::CardinalityExpr, h::UInt) = hash((:Expr, e.op, e.args), h)

# Cardinal arithmetic in two layers:
#  (a) explicit pairs of *concrete* cardinalities (Finite, CountablyInfinite, Continuum);
#  (b) a generic fallback for any combination involving Symbolic / Expr.
# Splitting this way avoids dispatch ambiguities.

# (a) Concrete × concrete

# Addition.
+(a::Finite, b::Finite) = Finite(a.n + b.n)
+(::Finite, b::CountablyInfinite) = b
+(a::CountablyInfinite, ::Finite) = a
+(::CountablyInfinite, ::CountablyInfinite) = CountablyInfinite()
+(::Finite, b::Continuum) = b
+(a::Continuum, ::Finite) = a
+(::CountablyInfinite, b::Continuum) = b
+(a::Continuum, ::CountablyInfinite) = a
+(::Continuum, ::Continuum) = Continuum()

# Multiplication. 0 absorbs.
*(a::Finite, b::Finite) = Finite(a.n * b.n)
*(a::Finite, b::CountablyInfinite) = a.n == 0 ? Finite(0) : b
*(a::CountablyInfinite, b::Finite) = b.n == 0 ? Finite(0) : a
*(::CountablyInfinite, ::CountablyInfinite) = CountablyInfinite()
*(a::Finite, b::Continuum) = a.n == 0 ? Finite(0) : b
*(a::Continuum, b::Finite) = b.n == 0 ? Finite(0) : a
*(::CountablyInfinite, b::Continuum) = b
*(a::Continuum, ::CountablyInfinite) = a
*(::Continuum, ::Continuum) = Continuum()

# Exponentiation. n^ℵ₀ = 𝔠 for n ≥ 2.
^(a::Finite, b::Finite) = Finite(a.n ^ b.n)
^(a::Finite, ::CountablyInfinite) = a.n == 0 ? Finite(0) : a.n == 1 ? Finite(1) : Continuum()
^(::CountablyInfinite, b::Finite) = b.n == 0 ? Finite(1) : CountablyInfinite()
^(::CountablyInfinite, ::CountablyInfinite) = Continuum()
^(a::Continuum, b::Finite) = b.n == 0 ? Finite(1) : a
^(a::Continuum, ::CountablyInfinite) = a
^(::Continuum, ::Continuum) = Continuum()
^(a::Finite, ::Continuum) = a.n == 0 ? Finite(0) : a.n == 1 ? Finite(1) : Continuum()
^(::CountablyInfinite, ::Continuum) = Continuum()

# (b) Symbolic fallback with simplification + commutative canonicalization.
#
# Rules:
#   0 + x → x   ;  x + 0 → x
#   0 · x → 0   ;  x · 0 → 0
#   1 · x → x   ;  x · 1 → x
#   x ^ 1 → x   ;  1 ^ x → 1   ;  x ^ 0 → 1
# For + and ·, arguments are sorted by `_card_key` so that `|A| + |B|`
# and `|B| + |A|` produce equal expressions.

const _SymbolicAny = Union{SymbolicCardinality,CardinalityExpr}

"Total order key used for canonicalization of commutative ops; not exposed as `isless`."
_card_key(c::Cardinality) = sprint(show, c)

function _build_add(a::Cardinality, b::Cardinality)
    a == Finite(0) && return b
    b == Finite(0) && return a
    ka, kb = _card_key(a), _card_key(b)
    ka ≤ kb ? CardinalityExpr(:+, (a, b)) : CardinalityExpr(:+, (b, a))
end

function _build_mul(a::Cardinality, b::Cardinality)
    (a == Finite(0) || b == Finite(0)) && return Finite(0)
    a == Finite(1) && return b
    b == Finite(1) && return a
    ka, kb = _card_key(a), _card_key(b)
    ka ≤ kb ? CardinalityExpr(:*, (a, b)) : CardinalityExpr(:*, (b, a))
end

function _build_pow(a::Cardinality, b::Cardinality)
    b == Finite(0) && return Finite(1)
    b == Finite(1) && return a
    a == Finite(1) && return Finite(1)
    CardinalityExpr(:^, (a, b))
end

+(a::_SymbolicAny, b::Cardinality)  = _build_add(a, b)
+(a::Cardinality, b::_SymbolicAny)  = _build_add(a, b)
+(a::_SymbolicAny, b::_SymbolicAny) = _build_add(a, b)

*(a::_SymbolicAny, b::Cardinality)  = _build_mul(a, b)
*(a::Cardinality, b::_SymbolicAny)  = _build_mul(a, b)
*(a::_SymbolicAny, b::_SymbolicAny) = _build_mul(a, b)

^(a::_SymbolicAny, b::Cardinality)  = _build_pow(a, b)
^(a::Cardinality, b::_SymbolicAny)  = _build_pow(a, b)
^(a::_SymbolicAny, b::_SymbolicAny) = _build_pow(a, b)

# Display
show(io::IO, c::Finite) = print(io, c.n)
show(io::IO, ::CountablyInfinite) = print(io, "ℵ₀")
show(io::IO, ::Continuum) = print(io, "𝔠")
show(io::IO, s::SymbolicCardinality) = print(io, "|", s.name, "|")
function show(io::IO, e::CardinalityExpr)
    sym = e.op == :^ ? "^" : e.op == :* ? "·" : "+"
    print(io, "(")
    show(io, e.args[1])
    print(io, sym)
    show(io, e.args[2])
    print(io, ")")
end

"True iff the cardinality is `Finite(n)` for some `n`."
isfinite_card(c::Cardinality) = c isa Finite
