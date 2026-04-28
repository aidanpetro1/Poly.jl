# ============================================================
# Monoidal products on Polynomial and Lens (Sprint 3)
# ============================================================
#
# This file implements the three concrete-layer monoidal products from
# Niu & Spivak Chapter 3:
#
#   +   coproduct      (unit: zero_poly)
#   *   cartesian      (unit: one_poly)         — also written `×`
#   ⊗   parallel       (unit: y)                — also `parallel`
#
# Symbolic counterparts and the full rewrite-rule set live in `Symbolic.jl`.
#
# Eager representation: when both operand position-sets are FinPolySet, the
# resulting position-set is also a FinPolySet of tuples. For + we use tagged
# pairs `(1, i)` / `(2, j)`; for × and ⊗ we use plain pairs `(i, j)`. Symbolic
# / non-finite operands fall through to an error directing the user to the
# symbolic layer (where the operations build expression trees instead).

# ============================================================
# Coproduct  +
# ============================================================

"""
    +(p::Polynomial, q::Polynomial) -> Polynomial

The coproduct in **Poly**. Positions tagged: `(1, i)` from `p`, `(2, j)`
from `q`. Direction-sets inherited from each side.
"""
function +(p::Polynomial, q::Polynomial)
    pp, qp = p.positions, q.positions
    if !(pp isa FinPolySet && qp isa FinPolySet)
        error("Concrete + requires finite position-sets; for symbolic operands " *
              "use the SymbolicPolynomial layer.")
    end
    elts = Tuple{Int,Any}[]
    for i in pp.elements; push!(elts, (1, i)); end
    for j in qp.elements; push!(elts, (2, j)); end
    new_pos = FinPolySet(elts)
    new_dir = key -> begin
        tag, val = key
        tag == 1 ? direction_at(p, val) : direction_at(q, val)
    end
    Polynomial(new_pos, new_dir)
end

"""
    +(f::Lens, g::Lens) -> Lens

Bifunctor action of `+` on lenses: `f + g : dom(f)+dom(g) → cod(f)+cod(g)`.
"""
function +(f::Lens, g::Lens)
    new_dom = f.dom + g.dom
    new_cod = f.cod + g.cod
    on_pos = key -> begin
        tag, val = key
        tag == 1 ? (1, f.on_positions.f(val)) : (2, g.on_positions.f(val))
    end
    on_dir = (key, b) -> begin
        tag, val = key
        if tag == 1
            f.on_directions.f(val).f(b)
        else
            g.on_directions.f(val).f(b)
        end
    end
    Lens(new_dom, new_cod, on_pos, on_dir)
end

# ============================================================
# n-ary flat coproduct
# ============================================================

"""
    coproduct(ps::Polynomial...) -> Polynomial

n-ary disjoint union of polynomials. Positions are flat-tagged as
`(k, x)` where `k` is the 1-based operand index and `x` is a position
from `ps[k]`. Equivalent in semantics to `ps[1] + ps[2] + ... + ps[n]`
but produces flat tags rather than the nested `(1, (1, ..., (1, x)))`
chain that left-associated binary `+` produces.

Compare:

    (p_a + p_b + p_c).positions  # tags (1, (1, x_a)), (1, (2, x_b)), (2, x_c)
    coproduct(p_a, p_b, p_c).positions  # tags (1, x_a), (2, x_b), (3, x_c)

For binary use, prefer `+` (book convention). For n-ary chains where the
nested tags become a navigation tax, prefer `coproduct`.

# Edge cases

  - `coproduct()` returns [`zero_poly`](@ref) (empty coproduct = initial object).
  - `coproduct(p)` returns `p` unchanged (no tagging needed for a single operand).
"""
# Zero-arg method to disambiguate between `Polynomial...` and `Lens...`
# varargs (both match the empty call). Returns the initial object in **Poly**.
coproduct() = zero_poly

function coproduct(ps::Polynomial...)
    length(ps) == 1 && return ps[1]

    for (k, p) in enumerate(ps)
        p.positions isa FinPolySet ||
            error("coproduct: operand $k has non-finite positions; " *
                  "use the SymbolicPolynomial layer.")
    end

    elts = Tuple{Int,Any}[]
    for (k, p) in enumerate(ps)
        for x in p.positions.elements
            push!(elts, (k, x))
        end
    end
    new_pos = FinPolySet(elts)
    new_dir = key -> begin
        k, x = key
        direction_at(ps[k], x)
    end
    Polynomial(new_pos, new_dir)
end

"""
    coproduct(fs::Lens...) -> Lens

n-ary version of `+(f::Lens, g::Lens)`. Domains and codomains are combined
via `coproduct` of polynomials; positions and directions are routed through
whichever operand they originated in.
"""
function coproduct(fs::Lens...)
    isempty(fs) && error("coproduct: empty lens coproduct undefined; pass at least one lens")
    length(fs) == 1 && return fs[1]

    new_dom = coproduct((f.dom for f in fs)...)
    new_cod = coproduct((f.cod for f in fs)...)
    on_pos = key -> begin
        k, x = key
        (k, fs[k].on_positions.f(x))
    end
    on_dir = (key, b) -> begin
        k, x = key
        fs[k].on_directions.f(x).f(b)
    end
    Lens(new_dom, new_cod, on_pos, on_dir)
end

"""
    flatten_coproduct(p::Polynomial) -> Polynomial

Take a polynomial whose positions are tagged in the left-associated binary-`+`
form and re-tag them into the flat form produced by [`coproduct`](@ref).
For an `n`-chain `(((p_1 + p_2) + p_3) + ... + p_n)`:

  - `p_1`'s positions appear as `(1, (1, ..., (1, x)))` with `n-1` ones
  - `p_k`'s positions (for `k > 1`) appear as `(1, ..., (1, (2, x)))` with `n-k` ones

`flatten_coproduct` walks each position to find the chain length `n` and
re-tags as `(operand_index, original_position)`.

Idempotent on already-flat polynomials whose positions don't happen to look
like `+`-chain tags.

# Limitation

Detection is structural and assumes the original operands' positions are not
themselves `(Int, _)` tuples whose first element is `1` or `2`. If they are,
the heuristic will mis-classify. In that case, prefer constructing the
polynomial via [`coproduct`](@ref) from the start.
"""
function flatten_coproduct(p::Polynomial)
    p.positions isa FinPolySet ||
        error("flatten_coproduct: requires FinPolySet positions; got $(typeof(p.positions))")

    # Pass 1: derive chain length n from the deepest 1-chain.
    n = 1
    decoded_tags = Vector{Tuple{Symbol,Int,Any}}()  # (kind, depth, orig)
    for x in p.positions.elements
        info = _coproduct_tag_walk(x)
        push!(decoded_tags, info)
        n = max(n, info[2] + 1)
    end

    # Pass 2: re-tag.
    new_elts = Tuple{Int,Any}[]
    for (kind, depth, orig) in decoded_tags
        operand = kind == :leftmost ? 1 : (n - depth)
        push!(new_elts, (operand, orig))
    end
    new_pos = FinPolySet(new_elts)

    # Direction: reconstruct the old tag for lookup.
    new_dir = key -> begin
        k, orig = key
        old_tag = _coproduct_tag_build(k, orig, n)
        direction_at(p, old_tag)
    end
    Polynomial(new_pos, new_dir)
end

# Walk a left-associated +-chain tag, counting leading 1s and reporting how
# the descent terminated.
#
# Returns `(kind, depth, original_position)`:
#   - kind = :leftmost — descended through `depth` ones and then ran out of
#     `(Int, _)` structure. The descent never hit a 2; this is the leftmost
#     operand, regardless of chain length.
#   - kind = :hit_2 — descended through `depth` ones and then encountered
#     a 2-tagged tuple. The original position is the rest of that tuple.
function _coproduct_tag_walk(tag)
    depth = 0
    current = tag
    while current isa Tuple && length(current) == 2 && current[1] isa Int
        head, rest = current
        if head == 1
            depth += 1
            current = rest
        elseif head == 2
            return (:hit_2, depth, rest)
        else
            error("flatten_coproduct: unexpected tag head $head; expected 1 or 2 in a binary-+ chain")
        end
    end
    return (:leftmost, depth, current)
end

# Reconstruct the original left-associated +-chain tag from a flat
# `(operand_index, original_position)` plus the chain length.
function _coproduct_tag_build(k::Int, orig, n::Int)
    if k == 1
        result = orig
        for _ in 1:(n-1)
            result = (1, result)
        end
        return result
    else
        result = (2, orig)
        for _ in 1:(n-k)
            result = (1, result)
        end
        return result
    end
end

# ============================================================
# Cartesian product  ×  (operator: *)
# ============================================================

"""
    *(p::Polynomial, q::Polynomial) -> Polynomial

The cartesian product in **Poly**. Positions are pairs `(i, j) ∈ p(1) × q(1)`;
direction-set at `(i, j)` is `p[i] + q[j]` represented as `FinPolySet` of
tagged pairs `(1, a)` / `(2, b)`.

Niu & Spivak Equation (3.61): `p × q ≅ Σ_{(i,j)} y^{p[i]+q[j]}`.
"""
function *(p::Polynomial, q::Polynomial)
    pp, qp = p.positions, q.positions
    if !(pp isa FinPolySet && qp isa FinPolySet)
        error("Concrete × requires finite position-sets; for symbolic operands " *
              "use the SymbolicPolynomial layer.")
    end
    elts = Tuple[]
    for i in pp.elements, j in qp.elements
        push!(elts, (i, j))
    end
    new_pos = FinPolySet(elts)
    new_dir = key -> begin
        i, j = key
        di = direction_at(p, i)
        dj = direction_at(q, j)
        if di isa FinPolySet && dj isa FinPolySet
            tagged = Tuple{Int,Any}[]
            for a in di.elements; push!(tagged, (1, a)); end
            for b in dj.elements; push!(tagged, (2, b)); end
            return FinPolySet(tagged)
        end
        SumSet(di, dj)
    end
    Polynomial(new_pos, new_dir)
end

"`p × q` — Unicode alias for [`*`](@ref) on polynomials."
const var"×" = (p::Polynomial, q::Polynomial) -> p * q

"""
    *(f::Lens, g::Lens) -> Lens

Bifunctor action of `×` on lenses.
"""
function *(f::Lens, g::Lens)
    new_dom = f.dom * g.dom
    new_cod = f.cod * g.cod
    on_pos = key -> begin
        i, j = key
        (f.on_positions.f(i), g.on_positions.f(j))
    end
    on_dir = (key, b_tagged) -> begin
        i, j = key
        side, b = b_tagged
        if side == 1
            (1, f.on_directions.f(i).f(b))
        else
            (2, g.on_directions.f(j).f(b))
        end
    end
    Lens(new_dom, new_cod, on_pos, on_dir)
end

# ============================================================
# Parallel product  ⊗  (Dirichlet)
# ============================================================

"""
    parallel(p::Polynomial, q::Polynomial) -> Polynomial

The parallel / Dirichlet product `p ⊗ q`. Positions `(i, j) ∈ p(1) × q(1)`;
direction-set at `(i, j)` is the cartesian product `p[i] × q[j]` represented
as a `FinPolySet` of pairs `(a, b)`.

Niu & Spivak Definition 3.65: `p ⊗ q ≅ Σ_{(i,j)} y^{p[i] × q[j]}`.
"""
function parallel(p::Polynomial, q::Polynomial)
    pp, qp = p.positions, q.positions
    if !(pp isa FinPolySet && qp isa FinPolySet)
        error("Concrete ⊗ requires finite position-sets; for symbolic operands " *
              "use the SymbolicPolynomial layer.")
    end
    elts = Tuple[]
    for i in pp.elements, j in qp.elements
        push!(elts, (i, j))
    end
    new_pos = FinPolySet(elts)
    new_dir = key -> begin
        i, j = key
        di = direction_at(p, i)
        dj = direction_at(q, j)
        if di isa FinPolySet && dj isa FinPolySet
            pairs = Tuple[]
            for a in di.elements, b in dj.elements
                push!(pairs, (a, b))
            end
            return FinPolySet(pairs)
        end
        ProductSet(di, dj)
    end
    Polynomial(new_pos, new_dir)
end

"`p ⊗ q` — Unicode alias for [`parallel`](@ref) on polynomials."
const var"⊗" = parallel  # binds the Unicode operator name to the function

"""
    parallel(f::Lens, g::Lens) -> Lens

Bifunctor action of `⊗` on lenses.
"""
function parallel(f::Lens, g::Lens)
    new_dom = parallel(f.dom, g.dom)
    new_cod = parallel(f.cod, g.cod)
    on_pos = key -> begin
        i, j = key
        (f.on_positions.f(i), g.on_positions.f(j))
    end
    on_dir = (key, b_pair) -> begin
        i, j = key
        a, b = b_pair
        (f.on_directions.f(i).f(a), g.on_directions.f(j).f(b))
    end
    Lens(new_dom, new_cod, on_pos, on_dir)
end

# ============================================================
# Composition product  ◁  (substitution / time evolution)
# ============================================================

"""
    subst(p::Polynomial, q::Polynomial) -> Polynomial

The composition product `p ◁ q` from Niu & Spivak Chapter 6 (Definition 6.1,
Equations 6.6/6.7). Positions are pairs `(i, j̄)` where `i ∈ p(1)` and `j̄`
is a `Dict` representing a function `p[i] → q(1)`. Direction-set at `(i, j̄)`
is the disjoint union `Σ_{a ∈ p[i]} q[j̄(a)]`, encoded as `FinPolySet` of
tagged pairs `(a, b)`.

Asymmetric: `(p, q) ↦ p ◁ q` and `(q, p) ↦ q ◁ p` are *not* related by
commutativity. Distributes only on the left over `+` and `×`.

For finite operands this enumerates all `j̄` functions; the count grows as
`Σ_i |q(1)|^|p[i]|`. For non-finite operands, use the SymbolicPolynomial layer.
"""
function subst(p::Polynomial, q::Polynomial)
    pp, qp = p.positions, q.positions
    if !(pp isa FinPolySet && qp isa FinPolySet)
        error("Concrete ◁ requires finite position-sets; for symbolic operands " *
              "use the SymbolicPolynomial layer.")
    end

    new_positions = Tuple[]
    for i in pp.elements
        Di = direction_at(p, i)
        Di isa FinPolySet ||
            error("Concrete ◁ requires finite direction-sets; got $(typeof(Di)) at p[$i]")
        if isempty(Di.elements)
            # Unique empty function ∅ → q(1).
            push!(new_positions, (i, Dict{eltype(Di),eltype(qp)}()))
        else
            for tup in Iterators.product((qp.elements for _ in Di.elements)...)
                jbar = Dict(zip(Di.elements, tup))
                push!(new_positions, (i, jbar))
            end
        end
    end
    new_pos_set = FinPolySet(new_positions)

    new_dir = key -> begin
        i, jbar = key
        Di = direction_at(p, i)::FinPolySet
        elts = Tuple[]
        for a in Di.elements
            j = jbar[a]
            Dj = direction_at(q, j)
            Dj isa FinPolySet ||
                error("Concrete ◁: q[$j] is $(typeof(Dj)); need FinPolySet")
            for b in Dj.elements
                push!(elts, (a, b))
            end
        end
        FinPolySet(elts)
    end

    Polynomial(new_pos_set, new_dir)
end

"""
    subst(f::Lens, g::Lens) -> Lens

Horizontal composition of lenses (Niu & Spivak Exercise 6.19).
`f : p → p'`, `g : q → q'` give `f ◁ g : p ◁ q → p' ◁ q'`.

On positions: `(i, j̄) ↦ (f₁ i, j̄')` where
`j̄'(a') = g₁(j̄(f♯_i(a')))` for `a' ∈ p'[f₁ i]`.

On directions at `(i, j̄)`: `(a', b') ↦ (f♯_i(a'), g♯_{j̄(f♯_i(a'))}(b'))`.
"""
function subst(f::Lens, g::Lens)
    p, p_prime = f.dom, f.cod
    q, q_prime = g.dom, g.cod
    new_dom = subst(p, q)
    new_cod = subst(p_prime, q_prime)

    on_pos = key -> begin
        i, jbar = key
        i_prime = f.on_positions.f(i)
        Di_prime = direction_at(p_prime, i_prime)::FinPolySet
        f_sharp_i = f.on_directions.f(i)::PolyFunction
        jbar_prime = Dict()
        for a_prime in Di_prime.elements
            a = f_sharp_i.f(a_prime)
            j = jbar[a]
            j_prime = g.on_positions.f(j)
            jbar_prime[a_prime] = j_prime
        end
        (i_prime, jbar_prime)
    end

    on_dir = (key, dest_pair) -> begin
        i, jbar = key
        a_prime, b_prime = dest_pair
        f_sharp_i = f.on_directions.f(i)::PolyFunction
        a = f_sharp_i.f(a_prime)
        j = jbar[a]
        g_sharp_j = g.on_directions.f(j)::PolyFunction
        b = g_sharp_j.f(b_prime)
        (a, b)
    end

    Lens(new_dom, new_cod, on_pos, on_dir)
end

"""
    subst_n(p::Polynomial, n::Integer) -> Polynomial

The n-fold composition product `p ◁ⁿ`. By convention, `p ◁⁰ = y` (the
unit) and `p ◁¹ = p`. Used in Sprint 6+ to model n-step dynamical-system
runs.

# Associativity note
For `n ≥ 3` we fold left-to-right: `subst_n(p, 3)` builds
`(p ◁ p) ◁ p`, not `p ◁ (p ◁ p)`. Mathematically the two are isomorphic
(`◁` is associative), but they will be `≈` rather than `==` because the
position-tuples are arranged differently.
"""
function subst_n(p::Polynomial, n::Integer)
    n < 0 && throw(ArgumentError("subst_n requires n ≥ 0; got $n"))
    n == 0 && return y
    n == 1 && return p
    result = p
    for _ in 2:n
        result = subst(result, p)
    end
    result
end

# Note on the operator: the book uses `◁` (U+25C1, white left-pointing
# triangle) for the composition product, but that character isn't in Julia's
# operator table. The nearest valid alternatives are:
#   * `⊲` (U+22B2) — at *comparison* precedence with chained-comparison
#     semantics (`a ⊲ b ⊲ c` parses as `(a ⊲ b) && (b ⊲ c)`), wrong for an
#     algebraic operator.
#   * `▷` (U+25B7, white right-pointing triangle) — at *multiplication*
#     precedence, which is what we want. Points the opposite direction
#     visually compared to the book's `◁`, but that's the price.
# We bind `▷` to `subst` so `p ▷ q` parses as infix. Source code
# referring to the book convention can still use `subst(p, q)`.
"`p ▷ q` — infix alias for [`subst`](@ref). The book's `◁` glyph is not a Julia operator; `▷` is the closest valid one."
const var"▷" = subst

# ============================================================
# Lazy composition product (LazySubst)
# ============================================================
#
# The eager `subst(p, q)` enumerates every j̄ : p[i] → q.positions for every
# i ∈ p.positions, producing `Σ_i |q.positions|^|p[i]|` positions. For
# non-trivial `p` (e.g. when many positions have several directions) this
# is an exponential blow-up that's unnecessary for type-checking against
# downstream operations like Bicomodule construction.
#
# `LazySubst` and its companion `SubstPolySet` defer that enumeration. The
# polynomial interface (`positions`, `direction_at`, cardinality) is
# implemented by computing what's asked, not by materializing the whole.
# Use `is_subst_of` (in this file) to check shape equality without
# enumeration; use `materialize` to force the eager form when actually
# needed.

"""
    SubstPolySet(p, q) <: PolySet

The position-set of `subst(p, q)` represented lazily. Mathematically the
set of pairs `(i, j̄)` where `i ∈ p.positions` and `j̄ : p[i] → q.positions`.

Cardinality is computed via the cardinality algebra without enumeration:

    |SubstPolySet(p, q)| = Σ_{i ∈ p.positions} |q.positions|^|p[i]|

`==` between two `SubstPolySet`s is structural on their `(p, q)` factors.
Iteration is intentionally not implemented — `LazySubst`'s value is in
*not* enumerating; if you genuinely need to walk the position-set, call
[`materialize`](@ref) on the corresponding `LazySubst` first.
"""
struct SubstPolySet <: PolySet
    p::AbstractPolynomial
    q::AbstractPolynomial
end

function cardinality(s::SubstPolySet)
    pp = positions(s.p)
    if pp isa FinPolySet
        cq = cardinality(positions(s.q))
        isempty(pp.elements) && return Finite(0)
        return reduce(+, (cq ^ cardinality(direction_at(s.p, i)) for i in pp))
    end
    SymbolicCardinality(Symbol("|", sprint(show, s.p), " ▷ ", sprint(show, s.q), "|"))
end

==(a::SubstPolySet, b::SubstPolySet) =
    _struct_equal(a.p, b.p) && _struct_equal(a.q, b.q)

# Structural equality on `AbstractPolynomial`s as used by lazy bookkeeping:
# two concretes compare by `==` (full structural); anything else falls
# back to identity here. The `LazySubst`-specific method is added below
# the `LazySubst` struct definition (forward-references aren't allowed in
# top-level Julia). Using dispatch instead of `isa`-branching keeps the
# rules legible and extensible — when a future lazy variant is added, it
# only needs its own method here.
_struct_equal(p::ConcretePolynomial, q::ConcretePolynomial) = p == q
_struct_equal(p::AbstractPolynomial, q::AbstractPolynomial) = p === q

hash(s::SubstPolySet, h::UInt) =
    hash((:SubstPolySet, _struct_hash(s.p), _struct_hash(s.q)), h)

# Hash mirrors `_struct_equal`: concretes hash structurally; non-concretes
# hash by identity, so the `(_struct_equal, _struct_hash)` pair stays consistent.
_struct_hash(p::ConcretePolynomial) = hash(p)
_struct_hash(p::AbstractPolynomial) = objectid(p)

function show(io::IO, s::SubstPolySet)
    print(io, "SubstPolySet(")
    show(io, s.p); print(io, ", "); show(io, s.q); print(io, ")")
end

# Cross-type equality with FinPolySet etc. is intentionally undefined — falls
# back to false. Use `is_subst_of(target_polynomial, p, q)` to check whether
# a concrete polynomial *is* the substitution shape.

"""
    LazySubst(p, q) <: AbstractPolynomial

A polynomial representing `subst(p, q)` (`p ▷ q`) without materializing its
position-set or direction-sets. The eager form has `Σ_i |q(1)|^|p[i]|`
positions, which can explode combinatorially for non-trivial `p`.
`LazySubst` defers all enumeration to the moment a position or direction-set
is queried, and supports lazy composition with itself
(`subst_lazy(LazySubst(p, q), r)` builds a tree of lazy substitutions
without materializing any intermediate).

Use [`subst_lazy`](@ref) as the constructor. Call [`materialize`](@ref) to
force the eager [`Polynomial`](@ref) form when an operation requires it.

# Polynomial interface

  - `positions(s)` returns a [`SubstPolySet`](@ref).
  - `direction_at(s, (i, j̄))` returns `Σ_a q[j̄(a)]` as a `FinPolySet` of
    tagged pairs `(a, b)`, computed without prior enumeration.
"""
struct LazySubst <: AbstractPolynomial
    p::AbstractPolynomial
    q::AbstractPolynomial
end

# Now that LazySubst exists, add its structural-equality / hash methods.
# These were declared in the abstract block above; extending them here
# keeps the dispatch story clean (one method per concrete subtype).
_struct_equal(p::LazySubst, q::LazySubst) =
    _struct_equal(p.p, q.p) && _struct_equal(p.q, q.q)
# Hash must mirror the recursive equality so == / hash invariants hold for
# Dict / Set: structurally-equal LazySubsts (with structurally-equal
# operands at every level) hash the same.
_struct_hash(p::LazySubst) =
    hash((:LazySubst, _struct_hash(p.p), _struct_hash(p.q)))

positions(s::LazySubst) = SubstPolySet(s.p, s.q)

"""
    direction_at(s::LazySubst, key) -> PolySet

Compute the direction-set of `s = subst(p, q)` at position `key = (i, j̄)`,
where `i ∈ p.positions` and `j̄` is a `Dict` representing `p[i] → q.positions`.
The result is `Σ_a q[j̄(a)]` as a `FinPolySet` of tagged pairs `(a, b)`,
matching the eager `subst` encoding.
"""
function direction_at(s::LazySubst, key)
    i, jbar = key
    Di = direction_at(s.p, i)
    Di isa FinPolySet ||
        error("LazySubst direction_at: p[$i] is $(typeof(Di)); need FinPolySet")
    elts = Tuple[]
    for a in Di.elements
        j = jbar[a]
        Dj = direction_at(s.q, j)
        Dj isa FinPolySet ||
            error("LazySubst direction_at: q[$j] is $(typeof(Dj)); need FinPolySet")
        for b in Dj.elements
            push!(elts, (a, b))
        end
    end
    FinPolySet(elts)
end

"""
    cardinality_of_apply(p::LazySubst, X::PolySet) -> Cardinality

`|(p ▷ q)(X)| = |p(q(X))|`. We compute through the cardinality algebra
without enumerating either intermediate, by routing `|q(X)|` and then
`|p(·)|` through [`_apply_cardinality`](@ref).
"""
function cardinality_of_apply(p::LazySubst, X::PolySet)
    cqX = _apply_cardinality(p.q, cardinality(X))
    _apply_cardinality(p.p, cqX)
end

# Internal: |poly(Y)| as a `Cardinality`, given just `|Y|`. Computes
# `Σ_i |Y|^|poly[i]|` via the cardinality algebra. Recurses into LazySubst
# operands without materialization.
function _apply_cardinality(poly::AbstractPolynomial, cY::Cardinality)
    pp = positions(poly)
    if pp isa FinPolySet
        isempty(pp.elements) && return Finite(0)
        return reduce(+, (cY ^ cardinality(direction_at(poly, i)) for i in pp))
    end
    SymbolicCardinality(Symbol("|poly(", cY, ")|"))
end

_apply_cardinality(poly::LazySubst, cY::Cardinality) =
    _apply_cardinality(poly.p, _apply_cardinality(poly.q, cY))

"""
    materialize(s::LazySubst) -> Polynomial

Force eager enumeration: returns `subst(p, q)` as a [`ConcretePolynomial`](@ref).
Operands that are themselves `LazySubst`s are materialized recursively first.

This is the escape hatch for code paths that genuinely need a fully
enumerated polynomial (e.g. structural `==`, `hash` participation,
old code paths that haven't been widened to `AbstractPolynomial`).
"""
function materialize(s::LazySubst)
    p_concrete = s.p isa LazySubst ? materialize(s.p) : s.p
    q_concrete = s.q isa LazySubst ? materialize(s.q) : s.q
    p_concrete isa ConcretePolynomial && q_concrete isa ConcretePolynomial ||
        error("materialize(LazySubst): operands must reduce to ConcretePolynomial; " *
              "got p=$(typeof(p_concrete)), q=$(typeof(q_concrete))")
    subst(p_concrete, q_concrete)
end

materialize(p::ConcretePolynomial) = p   # idempotent on concrete

==(a::LazySubst, b::LazySubst) = _struct_equal(a.p, b.p) && _struct_equal(a.q, b.q)

hash(s::LazySubst, h::UInt) = hash((:LazySubst, _struct_hash(s.p), _struct_hash(s.q)), h)

function show(io::IO, s::LazySubst)
    print(io, "LazySubst(")
    show(io, s.p); print(io, " ▷ "); show(io, s.q); print(io, ")")
end

"""
    subst_lazy(p, q) -> LazySubst

Lazy form of [`subst`](@ref): construct a polynomial representing `p ▷ q`
without enumerating positions or direction-sets. Equivalent in semantics to
`subst(p, q)` but defers all enumeration to query time. See [`LazySubst`](@ref).

Composes lazily with itself: `subst_lazy(subst_lazy(p, q), r)` returns a
`LazySubst` whose left operand is itself a `LazySubst`, with no intermediate
materialization.

# When to use

  - You're building a `Lens` or `Bicomodule` whose codomain is `subst(p, q)`
    and your bicomodule construction goes through [`is_subst_of`](@ref) for
    type-checking — no need to enumerate.
  - You're chaining substitutions (Ch. 6 n-step evolution) and only need
    the final result materialized.

# When `subst` is still the right tool

  - You need to inspect or iterate the resulting polynomial's positions
    directly. `materialize` first or call `subst` to begin with.
"""
subst_lazy(p::AbstractPolynomial, q::AbstractPolynomial) = LazySubst(p, q)

# Lazy composition: subst_lazy of a LazySubst stays lazy.
# (This is the same default method, but stating the dispatch makes the
# composition story explicit.)
subst_lazy(p::LazySubst, q::AbstractPolynomial) = LazySubst(p, q)
subst_lazy(p::AbstractPolynomial, q::LazySubst) = LazySubst(p, q)
subst_lazy(p::LazySubst, q::LazySubst) = LazySubst(p, q)

# ============================================================
# is_subst_of — shape-only equality predicate
# ============================================================

"""
    is_subst_of(target, p, q; force_enumerate=false) -> Bool

Test whether `target` is structurally equal to `subst(p, q)` (`p ▷ q`)
*without enumerating the substitution polynomial when possible*.

This is the predicate that unblocks `Bicomodule` construction over
substantial comonoids: instead of comparing `coaction.cod == subst(p, q)`
(which forces full enumeration of `Σ_i |q|^|p[i]|` j̄-functions), the
constructor checks shape with `is_subst_of`, which is `O(|p(1)|)` plus
one direction-set sample.

# Decision procedure (cheapest first)

  1. **Lazy short-circuit.** If `target isa LazySubst` and its operands
     match `(p, q)` structurally, return `true` immediately.
  2. **Cardinality check.** If `positions(target)` is finite, verify
     `|positions(target)| == Σ_i |q(1)|^|p[i]|` via the cardinality algebra.
     A mismatch returns `false` without touching any direction-sets.
  3. **Sample verification.** Pick one position from `target`, unpack it as
     `(i, j̄)`, and check shape: `i ∈ positions(p)`, `j̄ : p[i] → positions(q)`,
     and `|target[(i, j̄)]| == Σ_a |q[j̄(a)]|`. A wrong-shape target fails fast.
  4. **Strict equality (opt-in).** When `force_enumerate=true`, fall back to
     full structural `target == subst(p, q)`. Use only when the cheaper
     checks aren't enough and you can afford materialization.

# Soundness vs. completeness

Steps 1–3 are *sound* (false positives are not produced by any check that
matters in practice — the cardinality + sample together pin the shape down
for the well-behaved targets we expect). They are *not* fully complete:
a maliciously crafted polynomial whose positions match the right
cardinality and whose sampled position happens to look like `(i, j̄)` but
whose remaining positions disagree will pass the predicate. For
adversarial settings, pass `force_enumerate=true`.

# When you'd want `force_enumerate=true`

  - You're testing user-supplied or programmatically-generated polynomials
    where shape integrity isn't otherwise guaranteed.
  - You're at a debugging boundary and want certainty.

In normal Bicomodule construction (where the user has just built `cod`
themselves or via `subst`/`subst_lazy`), the cheap path is sufficient.
"""
function is_subst_of(target::AbstractPolynomial,
                     p::AbstractPolynomial,
                     q::AbstractPolynomial;
                     force_enumerate::Bool = false)
    # 1. Lazy short-circuit.
    if target isa LazySubst
        return _struct_equal(target.p, p) && _struct_equal(target.q, q)
    end

    # 2. Cardinality check.
    target_pos = positions(target)
    expected_card = _expected_subst_card(p, q)

    if target_pos isa FinPolySet && expected_card isa Finite
        length(target_pos.elements) == expected_card.n || return false
    elseif target_pos isa FinPolySet && !(expected_card isa Finite)
        # Target is finite but expected is infinite/symbolic — mismatch.
        return false
    end

    # If the target's positions can't be iterated, we can't sample. Defer
    # to the strict path if the caller asked, otherwise be conservative.
    if !(target_pos isa FinPolySet)
        return force_enumerate ? _strict_subst_check(target, p, q) : false
    end

    # 3. Sample verification: one position structurally.
    if isempty(target_pos.elements)
        return expected_card == Finite(0)
    end

    sample = first(target_pos.elements)
    sample isa Tuple && length(sample) == 2 || return false
    i, jbar = sample

    pp = positions(p)
    if pp isa FinPolySet
        i in pp.elements || return false
    end

    jbar isa AbstractDict || return false

    Di = direction_at(p, i)
    if Di isa FinPolySet
        Set(keys(jbar)) == Set(Di.elements) || return false
    end

    qp = positions(q)
    if qp isa FinPolySet
        all(j -> j in qp.elements, values(jbar)) || return false
    end

    target_dir = direction_at(target, sample)
    expected_dir_card = _direction_at_subst_card(p, q, sample)
    if target_dir isa FinPolySet && expected_dir_card isa Finite
        length(target_dir.elements) == expected_dir_card.n || return false
    end

    # 4. Optional strict check.
    force_enumerate && return _strict_subst_check(target, p, q)

    # Sample passed; that's the strongest claim available without enumerating.
    true
end

# Expected cardinality of `subst(p, q).positions` via the cardinality algebra.
function _expected_subst_card(p::AbstractPolynomial, q::AbstractPolynomial)
    pp = positions(p)
    if pp isa FinPolySet
        cq = cardinality(positions(q))
        isempty(pp.elements) && return Finite(0)
        return reduce(+, (cq ^ cardinality(direction_at(p, i)) for i in pp))
    end
    SymbolicCardinality(Symbol("|", sprint(show, p), " ▷ ", sprint(show, q), "|"))
end

# Expected cardinality of `subst(p, q)[(i, j̄)]` = Σ_a |q[j̄(a)]|.
function _direction_at_subst_card(p::AbstractPolynomial, q::AbstractPolynomial, key)
    i, jbar = key
    Di = direction_at(p, i)
    if Di isa FinPolySet
        isempty(Di.elements) && return Finite(0)
        return reduce(+, (cardinality(direction_at(q, jbar[a])) for a in Di.elements))
    end
    SymbolicCardinality(:dir_sum)
end

# Strict equality fallback — materializes anything lazy.
function _strict_subst_check(target::AbstractPolynomial,
                             p::AbstractPolynomial,
                             q::AbstractPolynomial)
    p_c = p isa LazySubst ? materialize(p) : p
    q_c = q isa LazySubst ? materialize(q) : q
    target_c = target isa LazySubst ? materialize(target) : target
    (p_c isa ConcretePolynomial && q_c isa ConcretePolynomial &&
     target_c isa ConcretePolynomial) || return false
    target_c == subst(p_c, q_c)
end

# ============================================================
# subst_targeted_lens — convenience constructor for lenses into subst(p, q)
# ============================================================
#
# Building a lens whose codomain is `subst(p, q)` requires the caller to
# manually thread the `(i, j̄)` position structure and the `(a, b)`
# direction structure. The reviewer of the original design hit this for
# every coaction of every bicomodule. `subst_targeted_lens` lets the
# caller write the natural shape — a single position-callback returning
# `(i, j̄)`, a single direction-callback receiving `(x, a, b)` — and
# handles the unpacking internally.
#
# Today the cod is built via eager `subst(p, q)` (because `Lens.cod` must
# be a `ConcretePolynomial`). PR #1's lazy work only unblocked the
# Bicomodule constructor's *type-check* against `subst(...)`. A future
# extension that widens `Lens.cod` to `AbstractPolynomial` would let this
# helper return a lens with a `LazySubst` cod, fully avoiding the
# enumeration; until then, this is purely an ergonomics win.

"""
    subst_targeted_lens(dom::Polynomial, p::Polynomial, q::Polynomial,
                        on_pos::Function, on_dir::Function) -> Lens

Build a lens `dom → subst(p, q)` (= `dom → p ▷ q`) from natural-shape
callbacks that don't require the user to assemble or unpack tuple
encodings of substitution-polynomial positions and directions.

# Callbacks

  - `on_pos(x) -> (i, j̄)` for `x ∈ dom.positions`, returning `i ∈ p.positions`
    and `j̄ : p[i] → q.positions` as a `Dict`.
  - `on_dir(x, a, b) -> dom_direction` for `x ∈ dom.positions`,
    `a ∈ p[i]`, and `b ∈ q[j̄(a)]` (where `(i, j̄) = on_pos(x)`). Returns
    a direction in `dom[x]`.

The helper wraps these so the resulting `Lens` honors the
substitution-polynomial encoding `(i, j̄)` for positions and `(a, b)` for
directions. A manually-constructed equivalent lens compares `==` to the
helper's output.

# Example — building the duplicator of a comonoid

```julia
# Comonoid duplicator δ : carrier → carrier ▷ carrier.
# Without the helper, the on_dir callback receives `(s, ab)` and has to
# unpack `a, b = ab` itself. With the helper, `(s, a, b)` arrives ready.
δ = subst_targeted_lens(carrier, carrier, carrier,
        s -> (s, Dict(t => t for t in S.elements)),
        (s, a, b) -> b)
```
"""
function subst_targeted_lens(dom::Polynomial, p::Polynomial, q::Polynomial,
                              on_pos::Function, on_dir::Function)
    cod = subst(p, q)
    wrapped_on_dir = (x, ab) -> begin
        a, b = ab
        on_dir(x, a, b)
    end
    Lens(dom, cod, on_pos, wrapped_on_dir)
end

# `subst_targeted_coaction` is the comonoid-side companion to the helper
# above. It depends on `Comonoid`, which is defined in `Comonoid.jl`
# (included after this file in `Poly.jl`'s top-level), so the function
# itself lives in `Cofree.jl` near `regular_bicomodule`. Reach for it
# when building a bicomodule's coaction lens.
