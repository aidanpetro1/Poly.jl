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
