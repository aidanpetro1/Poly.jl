# ============================================================
# Closure of ⊗, sections, derivative (Sprint 5)
# ============================================================
#
# This file implements the closure `[q, r]` of the parallel product ⊗ from
# Niu/Spivak Section 4.5, sections `Γ(p) = Poly(p, y)`, the do-nothing
# section on a state system, the canonical evaluation lens for `[q, r]`, and
# the derivative `ṗ`.
#
# Closure formula (Eq. 4.75 / Exercise 4.78):
#
#     [q, r] ≅ Σ_{f : q → r} y^{Σ_{j ∈ q(1)} r[f₁ j]}
#
# So a position of `[q, r]` *is* a lens `q → r`. We encode it as a tuple
# of `(i, g)` pairs, one per `j ∈ q(1)`, where `i ∈ r(1)` is `f₁(j)` and
# `g : r[i] → q[j]` is `f♯_j`. The k-th entry of the tuple corresponds to
# `q.positions.elements[k]`.
#
# This is the same encoding used by `apply(r, q[j])` (which produces
# `(i, g)` pairs), so we just take a product of those across `j`.

# ============================================================
# internal_hom — the closure [q, r]
# ============================================================

"""
    internal_hom(q::Polynomial, r::Polynomial) -> Polynomial

The closure `[q, r]` of the parallel product `⊗` (Niu/Spivak Eq. 4.75).
A position of `[q, r]` corresponds to a lens `q → r`; the direction-set at
that position is `Σ_{j ∈ q(1)} r[f₁ j]`, encoded as `FinPolySet` of `(j, b)`
pairs.

Satisfies the closure adjunction `Poly(p ⊗ q, r) ≅ Poly(p, [q, r])`
(Proposition 4.85).

Requires both `q.positions` and `r.positions` to be `FinPolySet`. For larger
polynomials the position-set of `[q, r]` is `Π_{j ∈ q(1)} |r(q[j])|` — grows
quickly; same combinatorial caveat as `subst`.
"""
function internal_hom(q::Polynomial, r::Polynomial)
    qp = q.positions
    rp = r.positions
    qp isa FinPolySet || error("internal_hom requires finite q.positions")
    rp isa FinPolySet || error("internal_hom requires finite r.positions")

    # Empty q → there is exactly one lens 0 → r (vacuous on positions).
    # The corresponding [0, r] has 1 position with 0 directions: i.e., 1.
    isempty(qp.elements) && return one_poly

    # For each j ∈ q.positions, list all (i, g) ∈ r(q[j]).
    choices = Vector{Vector{Tuple}}()
    for j in qp.elements
        Dj = direction_at(q, j)
        rqj = apply(r, Dj)
        rqj isa FinPolySet || error("internal_hom: r(q[$j]) is not finite")
        push!(choices, [c for c in rqj.elements])
    end

    new_positions = Tuple[]
    for combo in Iterators.product(choices...)
        push!(new_positions, combo)
    end
    pos_set = FinPolySet(new_positions)

    new_dir = combo -> begin
        elts = Tuple[]
        for (k, j) in enumerate(qp.elements)
            i, _g = combo[k]
            Di_r = direction_at(r, i)
            Di_r isa FinPolySet || error("internal_hom: r[$i] is not finite")
            for b in Di_r.elements
                push!(elts, (j, b))
            end
        end
        FinPolySet(elts)
    end

    Polynomial(pos_set, new_dir)
end

# ============================================================
# sections — Γ(p) = Poly(p, y)
# ============================================================

"""
    sections(p::Polynomial) -> FinPolySet

The set of sections of `p`. By Niu/Spivak Eq. (3.35),
`Γ(p) ≅ Π_{i ∈ p(1)} p[i]`: a section is a dependent function picking one
direction at each position of `p`.

Returned as a `FinPolySet` of `Dict` values mapping each position to a chosen
direction.
"""
function sections(p::Polynomial)
    pp = p.positions
    pp isa FinPolySet || error("sections requires finite p.positions")

    isempty(pp.elements) && return FinPolySet([Dict{Any,Any}()])

    direction_lists = []
    for i in pp.elements
        Di = direction_at(p, i)
        Di isa FinPolySet || error("sections: p[$i] is not finite")
        push!(direction_lists, [a for a in Di.elements])
    end

    secs = Dict[]
    for combo in Iterators.product(direction_lists...)
        push!(secs, Dict(zip(pp.elements, combo)))
    end
    FinPolySet(secs)
end

"""
    section_lens(p::Polynomial, σ::AbstractDict) -> Lens

Build the lens `p → y` corresponding to a particular section `σ`. `σ` should
map each `i ∈ p(1)` to a direction in `p[i]`.
"""
function section_lens(p::Polynomial, σ::AbstractDict)
    Lens(p, y, _ -> :pt, (i, _) -> σ[i])
end

# ============================================================
# do_nothing_section — the canonical ε for state systems
# ============================================================

"""
    do_nothing_section(S::PolySet) -> Lens

The do-nothing section `ε : Sy^S → y` on the state system over `S`. Picks
the direction-element-equal-to-the-position-element at every state.

This *is* the eraser of [`state_system_comonoid`](@ref) — that comonoid
literally calls this function to build its counit. The lens corresponds
to the contractible-groupoid structure on `S` where the identity at
state `s` is the "stay-put" arrow `s → s` (Niu/Spivak Example 4.43,
made comonoidal in Chapter 7).
"""
function do_nothing_section(S::PolySet)
    state_sys = monomial(S, S)
    Lens(state_sys, y, _ -> :pt, (i, _) -> i)
end

# ============================================================
# eval_lens — the canonical [q, r] ⊗ q → r
# ============================================================

"""
    eval_lens(q::Polynomial, r::Polynomial) -> Lens

The canonical evaluation lens `eval : [q, r] ⊗ q → r` (Niu/Spivak Eq. 4.88).
By the closure adjunction, this corresponds to the identity lens on `[q, r]`
under the natural isomorphism `Poly([q, r] ⊗ q, r) ≅ Poly([q, r], [q, r])`.

On positions: `(f, j) ↦ f₁(j)`.
On directions at `(f, j)`, given a direction `b ∈ r[f₁(j)]`:
the resulting `[q,r] ⊗ q` direction is the pair `((j, b), f♯_j(b))` —
the first component is the way `[q, r]`'s direction-set encodes the
`(position, directions)` pair, and the second is `f♯_j(b)` for the q-component.
"""
function eval_lens(q::Polynomial, r::Polynomial)
    qr = internal_hom(q, r)
    domain = parallel(qr, q)

    qp = q.positions
    qp isa FinPolySet || error("eval_lens requires finite q.positions")

    # Build a lookup: for each position-as-tuple `combo` of [q, r], and a
    # q-position `j`, find the (i, g) pair at index `k` (where j is the k-th
    # element of q.positions.elements).
    j_to_index = Dict(j => k for (k, j) in enumerate(qp.elements))

    on_pos = key -> begin
        # key is `(combo, j)` where combo is a tuple of (i, g) pairs.
        combo, j = key
        k = j_to_index[j]
        i, _ = combo[k]
        i
    end

    on_dir = (key, b) -> begin
        combo, j = key
        k = j_to_index[j]
        _i, g = combo[k]
        # The direction-set of `[q, r] ⊗ q` at (combo, j) is FinPolySet of
        # tagged pairs (1, qr_dir) and (2, q_dir) — see Monoidal.jl `*`/`⊗`.
        # Wait — `parallel`'s direction-set is a FinPolySet of (a, b) pairs
        # *not* tagged. Let me re-read… for `⊗`: directions are `p[i] × q[j]`
        # which we store as plain `(a, b)` pairs (no tag).
        # So the on-directions function returns a pair `(a, b)` where
        # `a` is a [q, r]-direction (which is a (j, b) tagged pair) and
        # `b` is a q[j]-direction.
        qr_dir = (j, b)         # the way [q, r] encodes directions
        q_dir  = g[b]           # f♯_j(b) — g is a Dict from r[i] to q[j]
        (qr_dir, q_dir)
    end

    Lens(domain, r, on_pos, on_dir)
end

# ============================================================
# derivative — ṗ
# ============================================================

"""
    derivative(p::Polynomial) -> Polynomial

The derivative `ṗ` of `p` (Niu/Spivak Example 3.22):

    ṗ = Σ_{i ∈ p(1)} Σ_{a ∈ p[i]} y^{p[i] − {a}}

Each position is a pair `(i, a)` with `i ∈ p(1)` and `a ∈ p[i]`; the
direction-set at `(i, a)` is `p[i]` minus `{a}`.

`ṗ(1)` (the position-set as a polynomial) is the set of all directions of
`p` — useful for the bundle `π_p`.
"""
function derivative(p::Polynomial)
    pp = p.positions
    pp isa FinPolySet || error("derivative requires finite p.positions")

    new_positions = Tuple[]
    for i in pp.elements
        Di = direction_at(p, i)
        Di isa FinPolySet || error("derivative: p[$i] is not finite")
        for a in Di.elements
            push!(new_positions, (i, a))
        end
    end
    pos_set = FinPolySet(new_positions)

    new_dir = key -> begin
        i, a = key
        Di = direction_at(p, i)::FinPolySet
        FinPolySet([b for b in Di.elements if b != a])
    end

    Polynomial(pos_set, new_dir)
end
