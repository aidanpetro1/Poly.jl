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
# coclosure — [q/p] (Prop 2.16, v0.6.1)
# ============================================================
#
# Spivak/Garner/Fairbanks Prop 2.16 (also: Niu/Spivak Remark 2.17 — left
# Kan extension of q along p):
#
#     [q/p] := Σ_{i ∈ p(1)} y^{q(p[i])}
#
# Coclosure adjunction: Poly([q/p], p') ≅ Poly(q, p' ◁ p).
#
# Examples (FA Example 2.18 lens shorthand):
#
#     [Q/P] (sets P, Q viewed as `constant` polynomials with empty
#     direction-sets) reduces to the lens-style notation `P y^Q`.
#
# This v0.6.1 implementation is the **finite** case: both `q.positions`
# and `p.positions` must be `FinPolySet`, and so must each direction-set
# `p[i]` (because we evaluate `apply(q, p[i])` for the direction-set of
# `[q/p]` at i, and `apply` requires finite shape for an enumerated
# return). The infinite / symbolic case (e.g. `coclosure(u, u)` with
# `u = list_polynomial()` over `NatSet()`) is deferred to v0.7.

"""
    coclosure(q::Polynomial, p::Polynomial) -> Polynomial

The coclosure `[q/p]` of `◁` from Spivak/Garner/Fairbanks Proposition 2.16.

Explicit formula:

    [q/p] := Σ_{i ∈ p(1)} y^{q(p[i])}.

Positions are `i ∈ p(1)`; the direction-set at `i` is `q(p[i])`, i.e.
`apply(q, direction_at(p, i))` — pairs `(j, g)` with `j ∈ q(1)` and
`g : q[j] → p[i]`.

Satisfies the **coclosure adjunction**:

    Poly([q/p], p′) ≅ Poly(q, p′ ◁ p)        (FA Eq. 17)

Equivalently (FA Remark 2.17), `[q/p]` is the **left Kan extension** of
`q` along `p` when both are viewed as polynomial endofunctors `Set → Set`.

# Special cases

  - `coclosure(constant(Q), constant(P)) ≅ P · y^Q` — the lens-shorthand
    of FA Example 2.18, since for `p = constant(P), q = constant(Q)`,
    every `p[i] = ∅` so `q(∅) = q(1) = Q` (after the empty-product
    convention) ... wait, that's not quite right; see the docstring
    example below for the exact reduction.
  - `coclosure(p, p)` carries a natural comonoid structure
    ([`comonoid_from_coclosure`](@ref), Example 5.5).

# Finite case only (v0.6.1)

Requires `q.positions` and `p.positions` to be `FinPolySet`, and every
`direction_at(p, i)` and `direction_at(q, j)` to be `FinPolySet`. The
infinite / symbolic case — most notably `coclosure(list_polynomial(),
list_polynomial())` over `NatSet()`, the construction Lemma 8.7 needs
to recover full Fin^op rather than a finite truncation — is deferred
to v0.7 alongside the multi-variable Dirichlet ⊗ on `d-Set[c]`.

# Example

```julia
P = constant(FinPolySet([:p1, :p2]))     # 2 positions, no directions
Q = linear(FinPolySet([:q]))              # 1 position, 1 direction
[Q/P] = coclosure(Q, P)
# Positions = P(1) = {:p1, :p2}.
# direction_at([Q/P], :p1) = apply(Q, P[:p1]) = apply(Q, ∅).
# Q has 1 position with 1 direction; Q(∅) has 0 positions (no map
# {:pt} → ∅), so direction_at([Q/P], :p1) is empty.
```

For a worked example with non-trivial directions, see
[`comonoid_from_coclosure`](@ref) which uses `coclosure(p, p)` as its
carrier.

See also: [`internal_hom`](@ref) (the closure of `⊗`),
[`comonoid_from_coclosure`](@ref) (Example 5.5 comonoid on `[p/p]`),
and [`apply`](@ref) (the underlying `q(X)` operation).
"""
function coclosure(q::Polynomial, p::Polynomial)
    pp = p.positions
    qp = q.positions
    pp isa FinPolySet ||
        error("coclosure: p.positions is $(typeof(pp)); v0.6.1 supports " *
              "FinPolySet only. v0.7 will install the symbolic / NatSet path.")
    qp isa FinPolySet ||
        error("coclosure: q.positions is $(typeof(qp)); v0.6.1 supports " *
              "FinPolySet only. v0.7 will install the symbolic / NatSet path.")

    # Validate finite direction-sets up front so the apply call below
    # gets a clear path. `apply(q, X)` works for X = FinPolySet when
    # every q[j] is FinPolySet.
    for j in qp.elements
        Dj = direction_at(q, j)
        Dj isa FinPolySet ||
            error("coclosure: q[$j] is $(typeof(Dj)); v0.6.1 needs " *
                  "FinPolySet for `apply(q, p[i])` to enumerate.")
    end
    for i in pp.elements
        Di = direction_at(p, i)
        Di isa FinPolySet ||
            error("coclosure: p[$i] is $(typeof(Di)); v0.6.1 needs " *
                  "FinPolySet for `apply(q, p[i])` to enumerate.")
    end

    # [q/p].positions = p.positions (each i ∈ p(1) gives one position).
    new_pos = pp

    # [q/p][i] = q(p[i]) = apply(q, direction_at(p, i)).
    # Returned by `apply` as a FinPolySet of pairs (j, g) with j ∈ q(1)
    # and g :: Dict mapping q[j].elements to p[i].elements.
    new_dir = i -> apply(q, direction_at(p, i))

    Polynomial(new_pos, new_dir)
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
