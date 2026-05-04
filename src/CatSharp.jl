# ============================================================
# Cat# inspection + duality bundle (v0.5.1 + v0.6 PolyAggregation prereqs)
# ============================================================
#
# The shipped subset of the bundle Spivak/Garner/Fairbanks call out in
# *Functorial Aggregation* (arXiv 2111.10968v7). v0.5.1 landed:
#
#   - `is_linear(::Bicomodule)` — Def 6.4 / Cor 6.17
#   - `LinearBicomodule(B)` — validate-and-wrap
#   - `linear_bicomodule_from_span(C, D, S, s, t; validate)` — Cor 6.17
#     forward direction (span → linear bicomodule)
#   - `c_one_y(c)` — Theorem 8.8 carrier as a self-bicomodule
#
# v0.6 (this file extends) adds the four PolyAggregation v0.3.0 prereqs:
#
#   - `bridge_diagram(::Bicomodule)` — Prop 3.20: extract the canonical
#     span-shape decomposition `(left_lens, right_lens)` from a bicomodule's
#     coactions. Structural primitive used by `aggregate_morphism`'s
#     row-routing and by `is_linear(::Bicomodule)`'s symbolic path.
#   - `span_from_linear_bicomodule(::LinearBicomodule)` — Cor 6.17 reverse
#     direction. Inverse of v0.5.1's `linear_bicomodule_from_span`.
#   - `weak_dual(p)` — single-variable Dirichlet weak dual `[p, y]`
#     (lives in `Monoidal.jl`).
#   - `comonoid_from_list_polynomial(u)` — Def 8.6 second half (lives in
#     `Demos.jl`).
#
# Items still pending v0.6: `is_conjunctive` + `ConjunctiveBicomodule`
# (Cor 6.15), a thin `Span{A,B}` struct + finite-set pullback in
# `compose(::Span, ::Span)`, and a convenience constructor
# `linear_bicomodule_from_span(span)`. None block PolyAggregation v0.3.0.

# ============================================================
# is_linear / LinearBicomodule — Def 6.4 + Cor 6.17
# ============================================================

"""
    is_linear(B::Bicomodule) -> Bool

Predicate: does `B` factor as `Σ_t ∘ Δ_s` for some span `(s, t)` of finite
sets, with no `Π` step? Equivalently: is the carrier of `B` of the form
`Sy` for some position-set `S` — every position has direction-set of size
exactly one. Equivalently (Cor 6.17 of Spivak/Garner/Fairbanks): is `B` a
left adjoint in `Cat#`?

This predicate is structural: when the carrier's positions are finite,
it inspects `direction_at(B.carrier, i)` for every `i` and checks each
has cardinality `Finite(1)`. When positions are infinite (e.g., `NatSet`),
exhaustive iteration isn't possible and the predicate returns `false`
conservatively, after a single `@info` noting the limitation. The fuller
treatment via bridge diagrams ships in v0.6 as `bridge_diagram`.

Coexists with the existing `is_linear(p::AbstractPolynomial)` predicate
via Julia's multiple dispatch — the polynomial form asks "is this a
linear polynomial `Iy`?", and the bicomodule form asks "is this a linear
bicomodule (carrier of the form `Sy`)?".
"""
function is_linear(B::Bicomodule)
    pos = positions(B.carrier)
    if pos isa FinPolySet
        for i in pos.elements
            cardinality(direction_at(B.carrier, i)) == Finite(1) || return false
        end
        return true
    end
    @info "is_linear(::Bicomodule): carrier positions are $(typeof(pos)); " *
          "exhaustive linearity check needs finite positions. Returning " *
          "false conservatively. v0.6 will land `bridge_diagram` for the " *
          "structural / symbolic case."
    false
end

"""
    LinearBicomodule(B::Bicomodule)

Typed wrapper asserting `is_linear(B)`. Construction errors if `B` is not
linear. Use this when you want type-level guarantees for downstream
operations that require the linear case (e.g. PolyAggregation's
`aggregate_along` query, which is morally a span `GROUP BY`).

`LinearBicomodule` does NOT mutate or normalize the underlying bicomodule
— it is a pure tag. Existing operations on `Bicomodule` lift through
`.underlying`. A future `normalize_linear` pass would be a separate
function; v0.5.1 does not ship one.

The wrapper is symmetric to `ConjunctiveBicomodule`, which ships in v0.6.
"""
struct LinearBicomodule
    underlying::Bicomodule
    function LinearBicomodule(B::Bicomodule)
        is_linear(B) ||
            error("LinearBicomodule: B is not linear " *
                  "(some position has direction-set of size ≠ 1)")
        new(B)
    end
end

function show(io::IO, L::LinearBicomodule)
    print(io, "LinearBicomodule(")
    show(io, L.underlying.carrier)
    print(io, ")")
end

# ============================================================
# linear_bicomodule_from_span — Cor 6.17 (forward direction)
# ============================================================

"""
    linear_bicomodule_from_span(
        C::Comonoid, D::Comonoid, S::FinPolySet,
        s::Function, t::Function;
        validate::Bool=true,
    ) -> LinearBicomodule

Build the linear bicomodule `Cy ▷ Sy ◁ Dy` corresponding to a span
`Ob(C) ←^s S →^t Ob(D)` between the object-sets of two comonoids.

Cor 6.17 of Spivak/Garner/Fairbanks: `Span(Set) ≃ Cat#_lin` as
bicategories; this constructor is one direction of that equivalence.
The carrier is `linear(S) = Sy` — every `x ∈ S` gives a position with
exactly one direction. Each `x` carries the trivial action: every
morphism of `C` at `s(x)` (resp. `D` at `t(x)`) factors through `x`,
so the direction action is the unique map to `:pt`.

  - `s :: Function` — maps each `x ∈ S` to a position of `C.carrier`.
  - `t :: Function` — maps each `x ∈ S` to a position of `D.carrier`.
  - `validate=true` — check `s(x) ∈ Ob(C)` and `t(x) ∈ Ob(D)` for every
    `x ∈ S`. Pass `false` to skip when constructing in tight loops.

Discrete bases (e.g. `discrete_comonoid(...)`) are the natural setting
for v0.5.1; non-discrete bases work via the trivial action when the
caller just needs to package a span as a bicomodule. The reverse
direction `span_from_linear_bicomodule`, the `Span{A,B}` struct, the
finite-set pullback in `compose(::Span, ::Span)`, and the convenience
constructor `linear_bicomodule_from_span(span)` ship in v0.6.

# Example

```julia
C = discrete_comonoid(FinPolySet([:customer]))
D = discrete_comonoid(FinPolySet([:order]))
S = FinPolySet([:o1, :o2, :o3])
B = linear_bicomodule_from_span(C, D, S,
        x -> :customer,           # s : S → Ob(C)
        x -> :order)              # t : S → Ob(D)
```
"""
function linear_bicomodule_from_span(C::Comonoid, D::Comonoid, S::FinPolySet,
                                     s::Function, t::Function;
                                     validate::Bool=true)
    if validate
        C_pos = positions(C.carrier)
        D_pos = positions(D.carrier)
        for x in S.elements
            sx = s(x)
            sx in C_pos ||
                error("linear_bicomodule_from_span: s($x) = $sx is not a " *
                      "position of left base C (positions: " *
                      "$(C_pos isa FinPolySet ? collect(C_pos.elements) : C_pos))")
            tx = t(x)
            tx in D_pos ||
                error("linear_bicomodule_from_span: t($x) = $tx is not a " *
                      "position of right base D (positions: " *
                      "$(D_pos isa FinPolySet ? collect(D_pos.elements) : D_pos))")
        end
    end

    carrier = linear(S)

    # Left coaction λ_L : carrier → C.carrier ▷ carrier.
    # At x ∈ S: position image is (s(x), jbar) where jbar(any C-direction) = x
    # — the trivial action ("every C-morphism at s(x) factors through x").
    # On directions, the substitution direction (a, :pt) maps to the unique
    # carrier-direction :pt.
    left_on_pos = x -> begin
        Cs = direction_at(C.carrier, s(x))
        Cs isa FinPolySet ||
            error("linear_bicomodule_from_span: C[s($x)] = C[$(s(x))] is " *
                  "$(typeof(Cs)); need FinPolySet for trivial-action " *
                  "construction. Use v0.6's bridge_diagram path for " *
                  "non-finite C.")
        (s(x), Dict(a => x for a in Cs.elements))
    end
    left_on_dir = (_x, _a, _b) -> :pt
    left_coaction = subst_targeted_coaction(carrier, C,
                                            left_on_pos, left_on_dir;
                                            side = :left)

    # Right coaction λ_R : carrier → carrier ▷ D.carrier.
    # At x ∈ S: position image is (x, ebar) where ebar(:pt) = t(x).
    # On directions, the substitution direction (e=:pt, b∈D[t(x)]) maps to
    # :pt (the unique direction of carrier[x]).
    right_on_pos = x -> (x, Dict(:pt => t(x)))
    right_on_dir = (_x, _a, _b) -> :pt
    right_coaction = subst_targeted_coaction(carrier, D,
                                             right_on_pos, right_on_dir;
                                             side = :right)

    B = Bicomodule(carrier, C, D, left_coaction, right_coaction)
    LinearBicomodule(B)
end

# ============================================================
# c_one_y — Theorem 8.8 carrier as a self-bicomodule
# ============================================================

"""
    c_one_y(c::Comonoid) -> LinearBicomodule

The linear bicomodule `c(1)y` of Spivak/Garner/Fairbanks Theorem 8.8 —
the carrier of the universal aggregator. Returned as a `c-1` bicomodule
(left base `c`, right base the unit comonoid `1 = discrete_comonoid({:pt})`),
which is the natural typing: `c(1)y` is a *left c-module* in the paper's
treatment, packaged as a bicomodule by trivializing the right side.

  - Carrier: `linear(positions(c.carrier))` — one position per object of
    `c`, each with the single direction `:pt`.
  - Left action: cod-tracking. A morphism `f : o → o'` of `c` at
    carrier-position `o` lifts the carrier to position `o' =
    cod_in_comonoid(c, o, f)`. Direction action collapses to `:pt`.
  - Right action: trivial (right base is the unit comonoid). Direction
    action collapses to `:pt`.

The right base is the unit comonoid (rather than `c` itself) because the
compatibility axiom of a `c-c` bicomodule forces the right action to be
constant in `o` whenever the left action is non-constant — which the
unit comonoid encodes cleanly. PolyAggregation v0.2.0 consumes
`c_one_y(c)` as the carrier for the homomorphism
`↻^α : c(1)y ◁ c → c(1)y` and only needs the left c-action; the right
side serves as the "no further action" cap that makes `compose` well-typed.

For a *discrete* `c`, the cod-tracking action collapses to the trivial
action, and `c_one_y(c)` is the same shape as
`linear_bicomodule_from_span(c, 1, positions(c.carrier), identity,
const :pt)` — but kept as its own constructor for discoverability and
because every PolyAggregation call site needing this carrier would
otherwise spell out the 6-line literal.

The dual `[c(1)y, y]` (via single-var Dirichlet weak duality) and the
conjunctive analog `c(1)y_con` ship in v0.6.
"""
function c_one_y(c::Comonoid)
    pos = positions(c.carrier)
    pos isa FinPolySet ||
        error("c_one_y: c has $(typeof(pos)) positions; v0.5.1 supports " *
              "FinPolySet only. v0.6's bridge_diagram path will lift the " *
              "restriction.")

    carrier = linear(pos)
    unit_comonoid = discrete_comonoid(FinPolySet([:pt]))

    # Left coaction λ_L : carrier → c.carrier ▷ carrier.
    # At carrier-position o ∈ Ob(c): position image is (o, jbar) where
    # jbar(f) = cod_in_comonoid(c, o, f). Direction action collapses to :pt.
    left_on_pos = o -> begin
        Co = direction_at(c.carrier, o)::FinPolySet
        # Read codomains directly from c.duplicator's on-positions image.
        # The duplicator's invariant is `on_positions.f(o) == (o, jbar)`.
        o_dup, jbar = c.duplicator.on_positions.f(o)
        o_dup == o ||
            error("c_one_y: duplicator on positions does not preserve " *
                  "first component at $o: got $o_dup")
        (o, Dict(f => jbar[f] for f in Co.elements))
    end
    left_on_dir = (_o, _f, _b) -> :pt
    left_coaction = subst_targeted_coaction(carrier, c,
                                            left_on_pos, left_on_dir;
                                            side = :left)

    # Right coaction λ_R : carrier → carrier ▷ unit_comonoid.carrier.
    # At carrier-position o: position image is (o, ebar) with ebar(:pt) = :pt
    # (the single object of the unit comonoid). All direction-side action is
    # forced to :pt — the only carrier-direction.
    right_on_pos = o -> (o, Dict(:pt => :pt))
    right_on_dir = (_o, _a, _b) -> :pt
    right_coaction = subst_targeted_coaction(carrier, unit_comonoid,
                                             right_on_pos, right_on_dir;
                                             side = :right)

    B = Bicomodule(carrier, c, unit_comonoid, left_coaction, right_coaction)
    LinearBicomodule(B)
end

# ============================================================
# span_from_linear_bicomodule — Cor 6.17 (reverse direction) — v0.6
# ============================================================

"""
    span_from_linear_bicomodule(L::LinearBicomodule) -> NamedTuple

Reverse direction of v0.5.1's [`linear_bicomodule_from_span`](@ref): given a
linear bicomodule `L`, recover the span data

    Ob(C) ←ˢ S →ᵗ Ob(D)

as a `NamedTuple` `(; C, D, S, s, t)` where

  - `C = L.underlying.left_base` (a `Comonoid`),
  - `D = L.underlying.right_base` (a `Comonoid`),
  - `S = positions(L.underlying.carrier)` (a `PolySet`, typically `FinPolySet`),
  - `s :: Function` — `x ∈ S ↦ position of C.carrier`,
  - `t :: Function` — `x ∈ S ↦ position of D.carrier`.

The `s`/`t` functions read directly off `L.underlying.left_coaction` and
`L.underlying.right_coaction`. For an Sy-shaped carrier (the linearity
hypothesis), the unique direction in `carrier[x]` is well-defined and
serves as the canonical handle for the right-coaction's position-chooser
`ebar` lookup.

# Round-trip with `linear_bicomodule_from_span`

For any span `(C, D, S, s, t)` between discrete bases:

```julia
sp_in  = (; C, D, S, s, t)
L      = linear_bicomodule_from_span(sp_in.C, sp_in.D, sp_in.S, sp_in.s, sp_in.t)
sp_out = span_from_linear_bicomodule(L)
# sp_out.s(x) == sp_in.s(x) and sp_out.t(x) == sp_in.t(x) for every x ∈ S.
```

The recovered `s`/`t` are extensionally equal to the inputs even though
they are fresh closures (they don't compare `===` to the originals).

# Special case: `c_one_y(c)`

`span_from_linear_bicomodule(c_one_y(c))` returns
`(; C=c, D=unit_comonoid, S=positions(c.carrier), s=identity, t=_->:pt)`.
The trivial right-leg encodes the c-1 packaging of `c(1)y`.

# Why now (PolyAggregation v0.3.0)

Promotes the private `_query_source` / `_query_target` accessors that
PolyAggregation hand-rolled against the v0.5.1 surface to a public Poly
API. Together with v0.5.1's `linear_bicomodule_from_span`, this realizes
**Cor 6.17 (Span(Set) ≃ Cat#_lin)** as a round-trippable equivalence at
the data level. Useful as a sanity check on `bridge_diagram` (#1).

Errors with a clear message if `L`'s carrier isn't of the form `Sy` —
unreachable through the `LinearBicomodule` wrapper since
[`is_linear(::Bicomodule)`](@ref) verifies linearity at construction
time, but kept as a defensive check for hand-built `LinearBicomodule`s
that bypass the wrapper.
"""
function span_from_linear_bicomodule(L::LinearBicomodule)
    B = L.underlying
    S = positions(B.carrier)

    # Defensive re-check: the wrapper enforces is_linear(B), but if a
    # caller hand-built B's carrier with a non-singleton direction-set at
    # any position, the right-leg lookup below would silently pick a
    # different "canonical" direction across calls. Surface that here.
    is_linear(B) ||
        error("span_from_linear_bicomodule: L.underlying is not linear " *
              "(carrier ≠ Sy). LinearBicomodule's wrapper should have " *
              "rejected this — check for hand-built construction that " *
              "bypassed the constructor.")

    # s : S → Ob(C). Read the first component of the left-coaction's
    # position image.
    #
    # By the bicomodule shape, B.left_coaction.on_positions.f(x) returns
    # (i, jbar) with i ∈ left_base.positions. For
    # `linear_bicomodule_from_span(C, D, S, s, t)`, that i is exactly
    # `s(x)`; for `c_one_y(c)`, it's `x` itself (the cod-tracking left
    # action's first component).
    s_fn = x -> begin
        x in S || error("span_from_linear_bicomodule: $x is not a position " *
                        "of L.underlying.carrier")
        B.left_coaction.on_positions.f(x)[1]
    end

    # t : S → Ob(D). Read the unique-direction lookup of the right-
    # coaction's position-chooser.
    #
    # For a linear carrier, `direction_at(B.carrier, x)` is a singleton
    # `FinPolySet`; let `b ∈ carrier[x]` be its sole element. Then
    # `B.right_coaction.on_positions.f(x) == (x, ebar)` with
    # `ebar :: carrier[x] → right_base.positions`, so `ebar[b]` is the
    # right-leg image. For
    # `linear_bicomodule_from_span(C, D, S, s, t)`, where `b == :pt`,
    # `ebar[:pt] == t(x)`; for `c_one_y(c)`, `ebar[:pt] == :pt` (the unit
    # comonoid's single object).
    t_fn = x -> begin
        x in S || error("span_from_linear_bicomodule: $x is not a position " *
                        "of L.underlying.carrier")
        Dx = direction_at(B.carrier, x)
        Dx isa FinPolySet ||
            error("span_from_linear_bicomodule: carrier[$x] is " *
                  "$(typeof(Dx)); the linearity check should have rejected " *
                  "this. Did the wrapper get bypassed?")
        # Linearity = singleton direction-set; `first` is well-defined.
        b = first(Dx.elements)
        _, ebar = B.right_coaction.on_positions.f(x)
        ebar[b]
    end

    (C = B.left_base, D = B.right_base, S = S, s = s_fn, t = t_fn)
end

# ============================================================
# bridge_diagram — Prop 3.20 (v0.6 → v0.7 promotion to full bridge)
# ============================================================
#
# v0.7 promotes v0.6's `bridge_diagram` from a `NamedTuple` to a typed
# `BridgeDiagram` struct carrying the **full** Prop 3.20 data
# `(B, E, π, S, T)` plus the v0.6 linear-case projection
# `(left_lens, right_lens)` for backward compatibility. The linear-case
# tests from v0.6 continue to pass because `bd.left_lens` /
# `bd.right_lens` still resolve to the same lenses.
#
# Discrete-base only in v0.7-partial: the elements category `E` is
# materialized as a set (i.e., its objects with no morphisms beyond
# identities). Endowing `E` with the morphisms from the bicomodule's
# right-coaction action requires the multi-variable polynomial
# infrastructure scheduled for the v0.7 main pass; the **set-level
# (B, E, π, S, T) data** shipped here is sufficient for every
# downstream consumer not directly inspecting Cat#'s 2-cell structure
# (notably PolyAggregation v0.3.x and PolyMarkov v0.1.x).

"""
    BridgeDiagram

The full Spivak/Garner/Fairbanks **Prop 3.20** bridge data for a
[`Bicomodule`](@ref). For a `(c, d)`-bicomodule with carrier
polynomial `m`, the corresponding prafunctor `c-Set → d-Set`
decomposes as `Σ_T ∘ Π_π ∘ Δ_S` with the diagram

           π
       E -----> B
     S/           \\T
    Ob(c)        Ob(d)

where:

  - `B = m(1)` is the position-set of the carrier,
  - `E = Σ_{i ∈ B} m[i]` is the elements-set (pairs `(i, a)` with
    `i ∈ B` and `a ∈ m[i]`),
  - `π : E → B` is the étale projection `(i, a) ↦ i` (its fibers
    `m[i]` recover the direction-set per position),
  - `S : B → Ob(c)` reads off the left coaction's first component,
  - `T : E → Ob(d)` reads off the right coaction's per-direction
    chooser (so `T(i, a) = ebar[a]` where
    `B.right_coaction.on_positions.f(i) == (i, ebar)`).

For backward compatibility with v0.6's `NamedTuple` return,
`BridgeDiagram` also exposes the **linear-case projection**
`(left_lens, right_lens)` as accessible fields.

# Discrete-base scope (v0.7-partial)

This v0.7-partial implementation materializes `E` as a finite set of
`(i, a)` tuples. Endowing `E` with the **categorical structure**
(morphisms induced by the bicomodule's right action) requires the
multi-variable polynomial infrastructure that ships in the v0.7 main
round. For the discrete-base case (both `left_base` and `right_base`
discrete comonoids) this is no loss; for general bases, `E`'s
identity-only morphisms are a faithful but incomplete view.

# Backward compatibility with v0.6

The v0.6 `bridge_diagram(B)` returned a `NamedTuple` `(; left_lens,
right_lens)`. v0.7's `BridgeDiagram` exposes the same `left_lens` and
`right_lens` fields, so all v0.6 call sites — `bd.left_lens`,
`bd.right_lens` — continue to resolve correctly. New v0.7 callers can
additionally access `bd.B`, `bd.E`, `bd.π`, `bd.S`, `bd.T`.

# Fields

  - `bicomodule :: Bicomodule` — the source bicomodule, kept for
    re-derivation and round-trip checks.
  - `B :: PolySet` — `positions(bicomodule.carrier)`.
  - `E :: FinPolySet` — elements as a set of `(i, a)` tuples (finite
    case only; v0.7-main extends to lazy enumeration).
  - `π :: Function` — `(i, a) ↦ i`.
  - `S :: Function` — `i ↦ position of left_base.carrier`.
  - `T :: Function` — `(i, a) ↦ position of right_base.carrier`.
  - `left_lens :: Lens` — v0.6 backward-compat: the left-leg projection.
  - `right_lens :: Lens` — v0.6 backward-compat: the right-leg projection.

See also: [`bridge_diagram`](@ref).
"""
struct BridgeDiagram
    bicomodule::Bicomodule
    B::PolySet
    E::FinPolySet
    π::Function
    S::Function
    T::Function
    left_lens::Lens
    right_lens::Lens
end

function show(io::IO, bd::BridgeDiagram)
    print(io, "BridgeDiagram(B=")
    show(io, bd.B)
    print(io, ", |E|=")
    print(io, cardinality(bd.E))
    print(io, ")")
end

"""
    bridge_diagram(B::Bicomodule) -> BridgeDiagram

Extract the bridge-diagram data per Spivak/Garner/Fairbanks
**Proposition 3.20**.

# Paper Prop 3.20 — full version (v0.7)

The full Prop 3.20 bridge associated to a prafunctor `c-Set → d-Set`
(equivalently a `(c, d)`-bicomodule) is a 5-tuple `(B, E, π, S, T)`
where `B = m(1)` is the position-set, `E = Σ_i m[i]` is the
elements-set, `π : E → B` is the étale projection `(i, a) ↦ i`,
`S : B → Ob(c)` is the left-leg, and `T : E → Ob(d)` is the right-leg.
The corresponding prafunctor decomposes as `Σ_T ∘ Π_π ∘ Δ_S`.

v0.7 promotes the v0.6 simplified return type from `NamedTuple` to a
typed [`BridgeDiagram`](@ref) struct carrying the full
`(B, E, π, S, T)` data. **Backward compatibility is preserved**: the
struct also exposes `left_lens` and `right_lens` as fields, so all
v0.6 callers (`bd.left_lens`, `bd.right_lens`) keep working unchanged.

# Returns:

  - `left_lens :: Lens` — `B.carrier → B.left_base.carrier`. Reads the
    first component of `B.left_coaction.on_positions` and projects the
    direction-action via the canonical-`b` choice (see below).
  - `right_lens :: Lens` — `B.carrier → B.right_base.carrier`. Reads
    `right_base`-positions out of `B.right_coaction.on_positions`'s
    chooser dict via the canonical carrier-direction.

For a *linear* bicomodule (carrier `Sy`), every `direction_at(B.carrier, x)`
is a singleton, the canonical-direction choice is unique, and the bridge
diagram exactly recovers the underlying span — `left_lens.on_positions`
agrees with `s` and `right_lens.on_positions` agrees with `t` from
[`span_from_linear_bicomodule`](@ref).

For a *general* bicomodule, the canonical direction is taken to be
`first(direction_at(B.carrier, x).elements)` — well-defined for
`FinPolySet` direction-sets. Empty direction-sets surface a clear error
at the offending position rather than producing a malformed lens.

# Why now (PolyAggregation v0.3.0)

`aggregate_morphism(inst)` constructs a `BicomoduleMorphism` whose
underlying lens needs the bridge structure of `c_one_y(c) ◁ c` to wire
up the row-routing on directions. Without `bridge_diagram`, the
construction has to reach into `c_one_y`'s internals (specifically the
right-coaction-into-unit-comonoid shape) — fragile across future
`LinearBicomodule` constructors. With `bridge_diagram`, the wiring is
structural.

Also useful as the symbolic / non-finite-positions path for
[`is_linear(::Bicomodule)`](@ref): the v0.5.1 implementation returns
`false` conservatively when positions aren't a `FinPolySet`. The bridge
makes it possible to ask "is the canonical-direction lookup well-defined
and singleton-valued at every probed position?" without exhaustive
enumeration. v0.6 doesn't ship that path yet — it's a follow-up that
the bridge unlocks.

# Cod-side caveat for non-`FinPolySet` direction-sets

The on-direction callback for `right_lens` looks up `ebar[b]` where
`b = first(carrier[x].elements)`. For symbolic / `LazySubst` direction-
sets, `first(...elements)` may not be defined. v0.6 surfaces a
`MethodError` at first call rather than at construction; v0.7's symbolic
generalization will install a structural fallback.

# Example

```julia
C = discrete_comonoid(FinPolySet([:c1, :c2]))
D = discrete_comonoid(FinPolySet([:d1, :d2]))
S = FinPolySet([:s1, :s2])
B = linear_bicomodule_from_span(C, D, S,
        x -> x === :s1 ? :c1 : :c2,
        x -> x === :s1 ? :d1 : :d2).underlying
bd = bridge_diagram(B)
bd.left_lens.on_positions.f(:s1)   # => :c1
bd.right_lens.on_positions.f(:s2)  # => :d2
```
"""
function bridge_diagram(B::Bicomodule)
    carrier = B.carrier
    cL = B.left_base.carrier
    cR = B.right_base.carrier

    # ----------------------------------------------------------
    # left_lens : carrier → left_base.carrier
    # ----------------------------------------------------------
    #
    # On positions: send x to the first component of B.left_coaction's
    # position image. By the bicomodule shape,
    # `B.left_coaction.on_positions.f(x) == (i, jbar)` with i ∈ cL(1).
    left_on_pos = x -> B.left_coaction.on_positions.f(x)[1]

    # On directions: at x with `i = left_on_pos(x)`, take a cL[i]-direction
    # `a` and produce a carrier[x]-direction.
    #
    # The substitution-polynomial direction at (i, jbar) is a pair (a, b)
    # with a ∈ cL[i] and b ∈ carrier[jbar(a)]. `B.left_coaction.on_directions`
    # accepts such an (a, b) and returns a carrier[x]-direction. To project
    # the bicomodule shape down to a lens, we need to drop the `b` index;
    # we do so by picking the *canonical* direction
    # `b_default = first(carrier[jbar(a)].elements)`. For a linear carrier
    # (every direction-set a singleton), `b_default` is unique and the
    # projection is loss-free.
    left_on_dir = (x, a) -> begin
        i, jbar = B.left_coaction.on_positions.f(x)
        # Defensive: a must lie in cL[i].
        Di = direction_at(cL, i)
        Di isa FinPolySet ||
            error("bridge_diagram(left_lens): cL[$i] is $(typeof(Di)); " *
                  "need FinPolySet to validate `a ∈ cL[i]`.")
        a in Di.elements ||
            error("bridge_diagram(left_lens): direction $a not in cL[$i] " *
                  "= $(collect(Di.elements))")
        # Canonical b: pick first carrier[jbar(a)] direction.
        j = jbar[a]
        Dj = direction_at(carrier, j)
        Dj isa FinPolySet ||
            error("bridge_diagram(left_lens): carrier[$j] is " *
                  "$(typeof(Dj)); need FinPolySet for canonical-b choice. " *
                  "v0.7 will install a symbolic fallback.")
        isempty(Dj.elements) &&
            error("bridge_diagram(left_lens): carrier[$j] is empty — " *
                  "no canonical direction available at position $x for " *
                  "left-leg projection. The bridge diagram is undefined " *
                  "for bicomodules with empty direction-sets at " *
                  "destination positions.")
        b = first(Dj.elements)
        B.left_coaction.on_directions.f(x).f((a, b))
    end

    left_lens = Lens(carrier, cL, left_on_pos, left_on_dir)

    # ----------------------------------------------------------
    # right_lens : carrier → right_base.carrier
    # ----------------------------------------------------------
    #
    # On positions: B.right_coaction.on_positions.f(x) == (x, ebar) with
    # `ebar : carrier[x] → cR(1)`. To pick a single right_base position,
    # take the canonical carrier-direction `b_canonical ∈ carrier[x]` and
    # read off `ebar[b_canonical]`. For a linear carrier this is unique.
    right_on_pos = x -> begin
        Dx = direction_at(carrier, x)
        Dx isa FinPolySet ||
            error("bridge_diagram(right_lens): carrier[$x] is " *
                  "$(typeof(Dx)); need FinPolySet for canonical-b choice. " *
                  "v0.7 will install a symbolic fallback.")
        isempty(Dx.elements) &&
            error("bridge_diagram(right_lens): carrier[$x] is empty — " *
                  "no canonical carrier-direction at position $x to feed " *
                  "the right-coaction's chooser dict. The bridge diagram " *
                  "is undefined at this position.")
        b = first(Dx.elements)
        _, ebar = B.right_coaction.on_positions.f(x)
        ebar[b]
    end

    # On directions: at x with `j = right_on_pos(x)`, take a cR[j]-direction
    # `a'` and produce a carrier[x]-direction.
    #
    # The substitution-polynomial direction at (x, ebar) is a pair (b, a')
    # with b ∈ carrier[x] and a' ∈ cR[ebar[b]]. We pass the canonical
    # `b_canonical = first(carrier[x].elements)` together with the user-
    # supplied `a'`.
    right_on_dir = (x, ap) -> begin
        Dx = direction_at(carrier, x)
        Dx isa FinPolySet ||
            error("bridge_diagram(right_lens): carrier[$x] is " *
                  "$(typeof(Dx)); need FinPolySet for canonical-b choice.")
        isempty(Dx.elements) &&
            error("bridge_diagram(right_lens): carrier[$x] is empty — " *
                  "cannot evaluate right-lens on directions.")
        b = first(Dx.elements)
        # Defensive: a' must lie in cR[ebar[b]].
        _, ebar = B.right_coaction.on_positions.f(x)
        j = ebar[b]
        Dj = direction_at(cR, j)
        Dj isa FinPolySet ||
            error("bridge_diagram(right_lens): cR[$j] is $(typeof(Dj)); " *
                  "need FinPolySet to validate `a' ∈ cR[j]`.")
        ap in Dj.elements ||
            error("bridge_diagram(right_lens): direction $ap not in " *
                  "cR[$j] = $(collect(Dj.elements))")
        B.right_coaction.on_directions.f(x).f((b, ap))
    end

    right_lens = Lens(carrier, cR, right_on_pos, right_on_dir)

    # ----------------------------------------------------------
    # Full Prop 3.20 (B, E, π, S, T) bridge data — v0.7
    # ----------------------------------------------------------
    #
    # B = m(1) = positions(carrier).
    # E = elements: pairs (i, a) with i ∈ B and a ∈ m[i].
    # π : E → B is the étale projection `(i, a) ↦ i`.
    # S : B → Ob(left_base) reads the left-coaction's first component.
    # T : E → Ob(right_base) reads the right-coaction's chooser at `a`.
    #
    # v0.7-partial: E materialized eagerly as a FinPolySet for finite
    # carriers. Lazy enumeration for non-finite carriers ships with the
    # v0.7 main pass.

    B_set = positions(carrier)

    # Build E if positions and direction-sets are finite. Surface a
    # clear error otherwise — the lazy / symbolic path is v0.7-main.
    elements_list = Tuple[]
    if B_set isa FinPolySet
        for i in B_set.elements
            Di = direction_at(carrier, i)
            Di isa FinPolySet ||
                error("bridge_diagram: carrier[$i] is $(typeof(Di)); v0.7-" *
                      "partial requires FinPolySet for E enumeration. " *
                      "v0.7-main extends to lazy E.")
            for a in Di.elements
                push!(elements_list, (i, a))
            end
        end
    else
        error("bridge_diagram: positions(carrier) is $(typeof(B_set)); " *
              "v0.7-partial requires FinPolySet for E enumeration. " *
              "v0.7-main extends to lazy E.")
    end
    E_set = FinPolySet(elements_list)

    # π : E → B is the étale projection `(i, a) ↦ i`. Implemented as a
    # plain function on the (i, a) tuple (the canonical encoding of E
    # elements above).
    π_fn = ia -> ia[1]

    # S : B → Ob(left_base.carrier). Reads the left-coaction's
    # position image's first component. For `linear_bicomodule_from_span(C,
    # D, S, s, t)` this is exactly `s`; for `c_one_y(c)` it's identity on
    # objects of c (the cod-tracking left action).
    S_fn = i -> B.left_coaction.on_positions.f(i)[1]

    # T : E → Ob(right_base.carrier). Reads the right-coaction's
    # chooser dict at the per-element direction `a`. For
    # `linear_bicomodule_from_span(C, D, S, s, t)` this collapses to
    # `t(i)` (since carrier[i] is a singleton {:pt} and ebar[:pt] =
    # t(i)); for general bicomodules it's the per-direction action.
    T_fn = ia -> begin
        i, a = ia
        _, ebar = B.right_coaction.on_positions.f(i)
        ebar[a]
    end

    BridgeDiagram(B, B_set, E_set, π_fn, S_fn, T_fn,
                  left_lens, right_lens)
end
