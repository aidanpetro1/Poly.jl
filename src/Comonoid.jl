# ============================================================
# Comonoids in (Poly, y, ▷) — they ARE categories (Sprint 7)
# ============================================================
#
# This file implements the Ahman–Uustalu correspondence
#
#       Comon(Poly, y, ▷)  ≃  Cat#
#
# A comonoid in (Poly, y, ▷) is a triple (c, ε, δ) where
#
#     ε : c → y          (counit / "eraser")
#     δ : c → c ▷ c      (comultiplication / "duplicator")
#
# satisfying counit and coassociativity axioms. Niu/Spivak Chapter 7
# (following Ahman–Uustalu) shows that giving such a comonoid is the same
# as giving a (small) category whose objects are c.positions and whose
# morphisms out of i are the directions c[i]. The eraser picks out the
# identity at each object; the duplicator encodes (codomain, composition).
#
# We make this concrete by translating between two representations:
#
#   * `Comonoid` — the polynomial-level data (carrier, eraser, duplicator).
#   * `SmallCategory` — explicit object/morphism tables with identity and
#     composition Dicts.
#
# `to_category` and `from_category` round-trip; `validate_comonoid` is
# implemented as `validate_category_laws ∘ to_category`. By the
# correspondence, the comonoid laws hold iff the resulting category is
# really a category.

# ============================================================
# Comonoid struct
# ============================================================

"""
    Comonoid(carrier::Polynomial, eraser::Lens, duplicator::Lens)

A comonoid in `(Poly, y, ▷)`. The constructor type-checks shapes:

- `eraser : carrier → y`           (the counit ε)
- `duplicator : carrier → carrier ▷ carrier`   (the comultiplication δ)

The counit/coassociativity *laws* are not checked at construction time —
use [`validate_comonoid`](@ref). By the Ahman–Uustalu correspondence
(Niu/Spivak Ch. 7) this is exactly the data of a small category whose
objects are `carrier.positions` and whose morphisms out of `i` are
`carrier[i]`.
"""
struct Comonoid
    carrier::Polynomial
    eraser::Lens
    duplicator::Lens
    function Comonoid(carrier::Polynomial, eraser::Lens, duplicator::Lens)
        eraser.dom == carrier ||
            error("Comonoid: eraser domain $(eraser.dom) ≠ carrier $carrier")
        eraser.cod == y ||
            error("Comonoid: eraser codomain $(eraser.cod) ≠ y")
        duplicator.dom == carrier ||
            error("Comonoid: duplicator domain $(duplicator.dom) ≠ carrier $carrier")
        # Shape-check via `is_subst_of` rather than computing `subst(carrier, carrier)`
        # eagerly and comparing structurally — that double-enumeration was the
        # type-check cost on the constructor. The eager `subst(...)` in the
        # *built-in* duplicator constructions (state_system_comonoid etc.)
        # below is a separate concern, addressed by `subst_targeted_lens`
        # (Extensions v1, PR #5).
        is_subst_of(duplicator.cod, carrier, carrier) ||
            error("Comonoid: duplicator codomain ≠ carrier ▷ carrier")
        new(carrier, eraser, duplicator)
    end
end

function show(io::IO, c::Comonoid)
    print(io, "Comonoid(")
    show(io, c.carrier)
    print(io, ")")
end

# ============================================================
# SmallCategory — explicit object/morphism tables
# ============================================================

"""
    SmallCategory(objects, morphisms, dom, cod, identity, composition)

A small category presented as five Dicts/sets:

- `objects::FinPolySet` — the objects.
- `morphisms::FinPolySet` — every morphism, encoded as a `(domain, direction)`
  pair so that morphisms with the same codomain but different domains stay
  distinct.
- `dom::Dict` — `morphism ↦ object` (the domain).
- `cod::Dict` — `morphism ↦ object` (the codomain).
- `identity::Dict` — `object ↦ morphism` (the identity at that object).
- `composition::Dict` — `(f, g) ↦ fg` for composable pairs (`cod(f) == dom(g)`),
  read left-to-right (`f` then `g`). Pairs that aren't composable are absent.

Build one from a `Comonoid` via [`to_category`](@ref); go the other way via
[`from_category`](@ref).
"""
struct SmallCategory
    objects::FinPolySet
    morphisms::FinPolySet
    dom::Dict
    cod::Dict
    identity::Dict
    composition::Dict
end

function show(io::IO, C::SmallCategory)
    print(io, "SmallCategory(",
          cardinality(C.objects), " objects, ",
          cardinality(C.morphisms), " morphisms)")
end

# ============================================================
# to_category — Comonoid → SmallCategory
# ============================================================

"""
    to_category(c::Comonoid) -> SmallCategory

Translate a comonoid in `(Poly, y, ▷)` into the category it presents.
Requires the carrier to have a finite position-set with finite direction-sets.

- Objects = `c.carrier.positions`.
- Morphisms = `(i, a)` pairs where `i ∈ positions` and `a ∈ c[i]`.
- `dom((i, a)) = i`.
- `cod((i, a))` is read off the duplicator's on-positions function.
- `identity(i)` is read off the eraser's on-directions function.
- `composition((i, a), (j, b))` (when `cod((i, a)) == j`) is read off the
  duplicator's on-directions function.
"""
function to_category(c::Comonoid)
    p = c.carrier
    pp = p.positions
    pp isa FinPolySet || error("to_category requires finite carrier positions")

    # Enumerate morphisms and tabulate dom/cod/identity from the lenses.
    morphisms_list = Tuple[]
    morphism_dom = Dict()
    morphism_cod = Dict()
    morphism_identity = Dict()

    for i in pp.elements
        Di = direction_at(p, i)
        Di isa FinPolySet ||
            error("to_category: c[$i] is $(typeof(Di)); need FinPolySet")

        # δ on positions: i ↦ (i, jbar) where jbar : c[i] → c.positions
        i_dup, jbar = c.duplicator.on_positions.f(i)
        i_dup == i ||
            error("Duplicator on positions does not preserve first component at $i: got $i_dup")

        for a in Di.elements
            morphism = (i, a)
            push!(morphisms_list, morphism)
            morphism_dom[morphism] = i
            morphism_cod[morphism] = jbar[a]
        end

        # ε on directions: at i, takes a single y-direction (:pt) to the
        # identity direction in c[i].
        ident_dir = c.eraser.on_directions.f(i).f(:pt)
        morphism_identity[i] = (i, ident_dir)
    end

    morphisms_set = FinPolySet(morphisms_list)

    # Build the composition table. δ on directions at i takes a (c ▷ c)-direction
    # (a, b) where a ∈ c[i], b ∈ c[jbar(a)], and returns the composite direction
    # in c[i]. So compose((i, a), (j, b)) = (i, δ♯_i(a, b)) when j = jbar(a).
    composition = Dict()
    for f in morphisms_list
        i, a = f
        j = morphism_cod[f]
        Dj = direction_at(p, j)::FinPolySet
        for b in Dj.elements
            g = (j, b)
            composed_dir = c.duplicator.on_directions.f(i).f((a, b))
            composition[(f, g)] = (i, composed_dir)
        end
    end

    SmallCategory(pp, morphisms_set, morphism_dom, morphism_cod,
                  morphism_identity, composition)
end

# ============================================================
# from_category — SmallCategory → Comonoid
# ============================================================

"""
    from_category(C::SmallCategory) -> Comonoid

Reverse direction: package a `SmallCategory` as a comonoid in `(Poly, y, ▷)`.

The carrier polynomial has objects as positions, with the direction-set at
each object `o` being the set of directions of morphisms with `dom = o`
(the second components, since morphisms are encoded as `(dom, direction)`).
"""
function from_category(C::SmallCategory)
    out_directions = Dict{Any,Vector{Any}}()
    for o in C.objects.elements
        out_directions[o] = Any[]
    end
    for f in C.morphisms.elements
        d = C.dom[f]
        push!(out_directions[d], f[2])
    end

    carrier = Polynomial(C.objects,
                         i -> FinPolySet(out_directions[i]))

    # Eraser at i picks the second component of identity[i]
    eraser = Lens(carrier, y, _ -> :pt, (i, _) -> C.identity[i][2])

    # Duplicator on positions: i ↦ (i, jbar) where jbar(a) = cod((i, a))
    dup_on_pos = i -> begin
        Di = direction_at(carrier, i)::FinPolySet
        jbar = Dict(a => C.cod[(i, a)] for a in Di.elements)
        (i, jbar)
    end
    # Duplicator on directions: at i, take (a, b) ↦ direction-component of
    # composition[(i, a), (cod((i,a)), b)].
    dup_on_dir = (i, ab) -> begin
        a, b = ab
        j = C.cod[(i, a)]
        f = (i, a)
        g = (j, b)
        C.composition[(f, g)][2]
    end

    # Use `subst_lazy` to avoid enumerating the substitution polynomial,
    # which has Σ_i |carrier(1)|^|carrier[i]| positions. With `Lens.cod`
    # widened to `AbstractPolynomial` and the `Comonoid` constructor's
    # cod-check going through `is_subst_of`, downstream consumption stays
    # lazy. Categorical-bridge `+`, `*`, `⊗` on `Comonoid` (which all go
    # through `from_category`) inherit the fix automatically.
    duplicator = Lens(carrier, subst_lazy(carrier, carrier),
                      dup_on_pos, dup_on_dir)

    Comonoid(carrier, eraser, duplicator)
end

# ============================================================
# Comonoid arithmetic (Extensions v1, PR #2)
# ============================================================
#
# `+`, `*`, `⊗` on Comonoid. These lift the corresponding categorical
# operations on small categories through the `to_category ↔ from_category`
# bridge. The bridge route is slower for large carriers (it enumerates
# every morphism explicitly via `to_category`) but it's mathematically
# unambiguous — the result is exactly the categorical coproduct / product
# of the underlying categories, transported back to the Comonoid form.
#
# `c ⊗ d` (Dirichlet/parallel) coincides with `c * d` (categorical
# product) on small categories — they're both products in `Cat#`. Both
# names are exposed for symmetry with `Polynomial`'s monoidal operators
# and to let users signal intent.

"""
    +(c::Comonoid, d::Comonoid) -> Comonoid

The coproduct of comonoids in `(Poly, y, ▷)`, equivalently the disjoint
union of the small categories they present (Niu/Spivak Ch. 7). Objects
and morphisms are tagged `(1, _)` for the `c`-side and `(2, _)` for the
`d`-side; composition only fires within a side.
"""
function +(c::Comonoid, d::Comonoid)
    cat_c = to_category(c)
    cat_d = to_category(d)

    # Tagged objects.
    objs = vcat([(1, o) for o in cat_c.objects.elements],
                [(2, o) for o in cat_d.objects.elements])
    # Tagged morphisms — `from_category` requires morphisms to be
    # `(domain, direction)` pairs, so we wrap the whole tagged morphism
    # as the direction component of a new (object, direction) pair.
    mors = vcat([((1, cat_c.dom[m]), (1, m)) for m in cat_c.morphisms.elements],
                [((2, cat_d.dom[m]), (2, m)) for m in cat_d.morphisms.elements])

    dom_dict = Dict{Any,Any}()
    cod_dict = Dict{Any,Any}()
    id_dict  = Dict{Any,Any}()
    comp_dict = Dict{Any,Any}()

    for m in cat_c.morphisms.elements
        wrapped = ((1, cat_c.dom[m]), (1, m))
        dom_dict[wrapped] = (1, cat_c.dom[m])
        cod_dict[wrapped] = (1, cat_c.cod[m])
    end
    for m in cat_d.morphisms.elements
        wrapped = ((2, cat_d.dom[m]), (2, m))
        dom_dict[wrapped] = (2, cat_d.dom[m])
        cod_dict[wrapped] = (2, cat_d.cod[m])
    end

    for o in cat_c.objects.elements
        id_orig = cat_c.identity[o]   # = (o, ident_dir)
        id_dict[(1, o)] = ((1, o), (1, id_orig))
    end
    for o in cat_d.objects.elements
        id_orig = cat_d.identity[o]
        id_dict[(2, o)] = ((2, o), (2, id_orig))
    end

    for ((f, g), h) in cat_c.composition
        wf = ((1, cat_c.dom[f]), (1, f))
        wg = ((1, cat_c.dom[g]), (1, g))
        wh = ((1, cat_c.dom[h]), (1, h))
        comp_dict[(wf, wg)] = wh
    end
    for ((f, g), h) in cat_d.composition
        wf = ((2, cat_d.dom[f]), (2, f))
        wg = ((2, cat_d.dom[g]), (2, g))
        wh = ((2, cat_d.dom[h]), (2, h))
        comp_dict[(wf, wg)] = wh
    end

    cat_sum = SmallCategory(FinPolySet(objs), FinPolySet(mors),
                            dom_dict, cod_dict, id_dict, comp_dict)
    from_category(cat_sum)
end

"""
    *(c::Comonoid, d::Comonoid) -> Comonoid

The categorical product of the small categories presented by `c` and `d`.
Objects are pairs `(x, y)`; morphisms are pairs `(m, n)` with
`dom(m, n) = (dom(m), dom(n))` and componentwise composition.

For small categories this coincides with `c ⊗ d` ([`⊗`](@ref) on Comonoid);
both names are exposed for parallelism with `Polynomial`'s operators.
"""
function *(c::Comonoid, d::Comonoid)
    cat_c = to_category(c)
    cat_d = to_category(d)

    objs = [(x, y) for x in cat_c.objects.elements
                       for y in cat_d.objects.elements]
    raw_mors = [(m, n) for m in cat_c.morphisms.elements
                           for n in cat_d.morphisms.elements]

    # Wrap each morphism as `(dom_pair, raw_morphism_pair)` so it lives in
    # the (domain, direction) shape that `from_category` requires.
    function wrap(mn)
        m, n = mn
        ((cat_c.dom[m], cat_d.dom[n]), mn)
    end
    mors = [wrap(mn) for mn in raw_mors]

    dom_dict = Dict{Any,Any}()
    cod_dict = Dict{Any,Any}()
    id_dict  = Dict{Any,Any}()
    comp_dict = Dict{Any,Any}()

    for mn in raw_mors
        m, n = mn
        w = wrap(mn)
        dom_dict[w] = (cat_c.dom[m], cat_d.dom[n])
        cod_dict[w] = (cat_c.cod[m], cat_d.cod[n])
    end

    for x in cat_c.objects.elements, y in cat_d.objects.elements
        id_pair = (cat_c.identity[x], cat_d.identity[y])
        id_dict[(x, y)] = wrap(id_pair)
    end

    for ((m1, m1_), m_comp) in cat_c.composition
        for ((n1, n1_), n_comp) in cat_d.composition
            f = wrap((m1, n1))
            g = wrap((m1_, n1_))
            h = wrap((m_comp, n_comp))
            comp_dict[(f, g)] = h
        end
    end

    cat_prod = SmallCategory(FinPolySet(objs), FinPolySet(mors),
                             dom_dict, cod_dict, id_dict, comp_dict)
    from_category(cat_prod)
end

"""
    ⊗(c::Comonoid, d::Comonoid) -> Comonoid

**Semantics changed in v0.3 (Extensions v2 PR #1, hard break).** Now an
alias for [`parallel(::Comonoid, ::Comonoid)`](@ref) (the carrier-tensor
matching `Polynomial ⊗`).

In v0.2 this delegated to [`*(::Comonoid, ::Comonoid)`](@ref)
(categorical product), which was inconsistent with `Polynomial`'s
operator naming. The v0.3 design originally planned a soft break with a
deprecation warning across one minor (`⊗` keeps v0.2 semantics in v0.3,
flips in v0.4), but the implementation revealed that `⊗` and `parallel`
are the *same function* via `const var"⊗" = parallel` in `Monoidal.jl`
— a method on one IS a method on the other. The two cannot disagree
for the same argument types. Per resolution 2026-05-01, the semantics
flip moved up to v0.3.

For users migrating from v0.2: replace `c ⊗ d` with `c * d` if you
wanted the categorical product (now the only way to get it). The new
`c ⊗ d` ≡ `parallel(c, d)` is the carrier-tensor; the two are iso as
comonoids but use different direction-set encodings (morphism-pair vs
direction-pair).
"""
# `⊗(::Comonoid, ::Comonoid)` is automatically aliased to
# `parallel(::Comonoid, ::Comonoid)` (defined below) via
# `const var"⊗" = parallel` in Monoidal.jl. No explicit method needed.

# ============================================================
# parallel(::Comonoid, ::Comonoid) — carrier-tensor (Extensions v2 PR #1)
# ============================================================
#
# The carrier-tensor of two comonoids: a comonoid whose carrier is the
# Polynomial-level parallel product `c.carrier ⊗ d.carrier`, with
# componentwise eraser and duplicator. This matches the direction-pair
# encoding used by `Polynomial ⊗` and by `parallel(::Bicomodule, ::Bicomodule)`,
# and differs from `*(::Comonoid, ::Comonoid)` (categorical product, which
# uses morphism-pair encoding via the `to_category ↔ from_category`
# bridge). The two are isomorphic but not structurally equal.
#
# Resolution log entry — design decision Q1.1 / Q1.2 (2026-05-01):
# this is the public surface; `_comonoid_carrier_tensor` is now a
# back-compat alias that points here.

"""
    parallel(c::Comonoid, d::Comonoid) -> Comonoid

The **carrier-tensor** of two comonoids: a comonoid whose carrier is
`parallel(c.carrier, d.carrier)` (i.e., `Polynomial ⊗`), with eraser
and duplicator computed componentwise from the operand comonoids.

This matches the direction-pair encoding used by `Polynomial ⊗` and is
the construction that pairs naturally with [`parallel(::Bicomodule, ::Bicomodule)`](@ref).
Use this when you want carriers to tensor as polynomials (e.g., joint
state spaces formed from per-component comonoids); use
[`*(::Comonoid, ::Comonoid)`](@ref) when you want the categorical
product (small categories: pairs of objects, pairs of morphisms).

The two constructions are isomorphic as comonoids but use different
direction encodings.

The result is validated at construction time (Q1.2 resolution): the
returned comonoid passes `validate_comonoid`. An invalid carrier-tensor
indicates a bug in the operand comonoids — surfaced by an error from
this constructor rather than silently propagating.

# Example

```julia
S = FinPolySet([:s1, :s2])
T = FinPolySet([:t1, :t2, :t3])
cs = state_system_comonoid(S)
ct = state_system_comonoid(T)

joint = parallel(cs, ct)
# joint.carrier === parallel(cs.carrier, ct.carrier)
# cardinality(joint.carrier.positions) == Finite(6)   # |S|·|T|
@assert validate_comonoid(joint)
```
"""
function parallel(c::Comonoid, d::Comonoid)
    new_carrier = parallel(c.carrier, d.carrier)

    new_eraser = Lens(new_carrier, y,
        _ -> :pt,
        (st, _pt) -> begin
            s, t = st
            c_id = c.eraser.on_directions.f(s).f(:pt)
            d_id = d.eraser.on_directions.f(t).f(:pt)
            (c_id, d_id)
        end)

    new_dup_on_pos = st -> begin
        s, t = st
        s_dup, jbar_c = c.duplicator.on_positions.f(s)
        t_dup, jbar_d = d.duplicator.on_positions.f(t)
        carrier_dirs = direction_at(new_carrier, st)::FinPolySet
        jbar_combined = Dict{Any,Any}()
        for ab in carrier_dirs.elements
            a, b = ab
            jbar_combined[ab] = (jbar_c[a], jbar_d[b])
        end
        ((s_dup, t_dup), jbar_combined)
    end
    new_dup_on_dir = (st, ab_pair) -> begin
        s, t = st
        # ab_pair = ((a1, a2), (b1, b2)).
        ab1, ab2 = ab_pair
        a1, a2 = ab1
        b1, b2 = ab2
        c_dir = c.duplicator.on_directions.f(s).f((a1, b1))
        d_dir = d.duplicator.on_directions.f(t).f((a2, b2))
        (c_dir, d_dir)
    end
    new_dup = Lens(new_carrier, subst_lazy(new_carrier, new_carrier),
                   new_dup_on_pos, new_dup_on_dir)

    result = Comonoid(new_carrier, new_eraser, new_dup)

    # Q1.2 (resolved 2026-05-01): validate at construction. The internal
    # `_comonoid_carrier_tensor` did not validate; the public surface does.
    # If both inputs are valid comonoids the result is valid by
    # construction, so this catches operand bugs rather than its own.
    validate_comonoid(result) ||
        error("parallel(::Comonoid, ::Comonoid): result failed " *
              "validate_comonoid; operands likely invalid")

    result
end

# ============================================================
# free_category_comonoid (Extensions v2, PR #14)
# ============================================================
#
# `free_category_comonoid(vertices, edges; max_depth)` builds the comonoid
# corresponding to the free category on a directed graph. Convenience
# wrapper over `from_category` that saves the user from constructing the
# `SmallCategory` by hand.
#
# Acyclic graphs: full free category. Every path is a distinct morphism;
# composition is path concatenation; identity is the empty path.
#
# Cyclic graphs: the free category is genuinely infinite. Per Q14.2
# (Extensions v2, 2026-05-01), this function takes a `max_depth` keyword
# and returns the depth-bounded truncation, emitting an `@warn` so the
# user knows the result is *not* a valid free comonoid (composites whose
# path length exceeds `max_depth` are filled in with a sentinel — the
# source identity — so the composition table stays total and downstream
# code like `validate_comonoid` runs without crashing; the sentinels are
# mathematically wrong, and `validate_comonoid` reports them as
# category-law failures, which is the structural form of "this isn't a
# valid free comonoid").

# Internal: detect a cycle in the directed graph via DFS with three colors.
# Returns true if any cycle reachable from any vertex.
function _graph_has_cycle(vertices, out_edges::Dict)
    WHITE, GRAY, BLACK = 0, 1, 2
    color = Dict{Any,Int}(v => WHITE for v in vertices)
    function dfs(v)
        color[v] = GRAY
        for (_, t) in out_edges[v]
            if color[t] == GRAY
                return true
            elseif color[t] == WHITE
                dfs(t) && return true
            end
        end
        color[v] = BLACK
        return false
    end
    for v in vertices
        if color[v] == WHITE
            dfs(v) && return true
        end
    end
    return false
end

# Internal: normalize a single edge into the canonical (src, tgt, label) form.
# Two-tuples auto-label by their position in the edges vector.
function _normalize_edge(e, autolabel::Int)
    if e isa Tuple
        if length(e) == 2
            return (e[1], e[2], autolabel)
        elseif length(e) == 3
            return (e[1], e[2], e[3])
        end
    end
    error("free_category_comonoid: edge $e has unexpected shape; " *
          "expected (src, tgt) or (src, tgt, label) tuple")
end

"""
    free_category_comonoid(vertices, edges; max_depth=nothing) -> Comonoid

Build the comonoid corresponding to the free category on a directed graph.

  - `vertices` — an `AbstractVector` (or anything with `collect`-able
    elements) of vertex labels.
  - `edges` — a `Vector` of edge tuples. Each tuple is either
    `(src, tgt)` (label auto-generated from position in the vector) or
    `(src, tgt, label)` (user-supplied label). Mixing the two forms in
    the same call is supported via per-edge dispatch on tuple arity.
  - `max_depth` — optional `Int`. Required when the graph contains
    cycles; ignored for acyclic graphs. Specifies the maximum path length
    to include in the truncation.

# Acyclic input

Returns the full free category as a `Comonoid`. Morphisms are paths
through the graph; identity at each vertex is the empty path; composition
is path concatenation. The result passes [`validate_comonoid`](@ref).

```julia
# Path: A → B → C
free_category_comonoid([:A, :B, :C], [(:A, :B), (:B, :C)])
```

# Cyclic input

The free category on a cyclic graph is infinite, so this function
truncates at `max_depth` and emits an `@warn`. **The truncated result
is not a valid free comonoid:** composites whose path-length would
exceed `max_depth` are filled in with a *sentinel* — the source identity
at the relevant domain — so the composition table stays total and
[`validate_comonoid`](@ref) runs cleanly rather than throwing. Because
the sentinels are mathematically wrong, validation returns `false` and
reports the category-law failures (typically associativity and identity
violations on the sentinel rows). The warning is the user's signal that
the truncation is in effect; the validation failures are the structural
manifestation of the same fact.

```julia
# Cyclic: A → B → A
free_category_comonoid([:A, :B], [(:A, :B), (:B, :A)]; max_depth=3)
# @warn: graph contains cycles; returning depth-bounded truncation...
```

For users who want the full lazy infinite version, the planned `LazyCofreeComonoid`
work (Extensions v2 #8) is the right tool once it lands.

# Mixed labeled / unlabeled edges

```julia
free_category_comonoid([:A, :B, :C],
                       [(:A, :B, :forward),     # explicitly labeled
                        (:B, :C),               # auto-labeled by position
                        (:A, :C, :shortcut)])
```
"""
function free_category_comonoid(vertices::AbstractVector, edges::AbstractVector;
                                max_depth::Union{Int,Nothing}=nothing)
    # Deduplicate vertices; preserve order.
    seen = Set{Any}()
    verts = Any[]
    for v in vertices
        v in seen || (push!(seen, v); push!(verts, v))
    end

    # Normalize edges; build adjacency.
    out_edges = Dict{Any,Vector{Tuple{Any,Any}}}(v => Tuple{Any,Any}[] for v in verts)
    edge_labels_seen = Dict{Any,Set{Any}}(v => Set{Any}() for v in verts)
    for (i, e) in enumerate(edges)
        s, t, l = _normalize_edge(e, i)
        s in seen || error("free_category_comonoid: edge source $s not in vertices")
        t in seen || error("free_category_comonoid: edge target $t not in vertices")
        l in edge_labels_seen[s] &&
            error("free_category_comonoid: duplicate edge label $l from vertex $s; " *
                  "supply explicit unique labels for parallel edges")
        push!(edge_labels_seen[s], l)
        push!(out_edges[s], (l, t))
    end

    # Cycle detection. Acyclic input: max_depth ignored. Cyclic + no
    # max_depth: error. Cyclic + max_depth: warn and truncate.
    has_cycle = _graph_has_cycle(verts, out_edges)
    if has_cycle && max_depth === nothing
        error("free_category_comonoid: graph contains cycles; supply `max_depth` " *
              "to get a depth-bounded truncation, or remove the cycles")
    end
    if has_cycle
        @warn "free_category_comonoid: graph contains cycles; returning depth-" *
              "bounded truncation (paths up to length $max_depth). The result is " *
              "NOT a valid free comonoid — `validate_comonoid` will report " *
              "missing compositions. See the docstring for details."
    end

    depth_bound = has_cycle ? max_depth : typemax(Int)

    # Enumerate morphisms: a morphism is `(start_vertex, label_tuple)`
    # where the label tuple is the empty `()` for the identity, or a
    # non-empty tuple of edge labels otherwise.
    morphisms = Tuple[]
    morphism_dom = Dict{Any,Any}()
    morphism_cod = Dict{Any,Any}()

    # Identity at each vertex.
    for v in verts
        m = (v, ())
        push!(morphisms, m)
        morphism_dom[m] = v
        morphism_cod[m] = v
    end

    # Non-empty paths: BFS from every vertex up to depth_bound.
    for start in verts
        # frontier = vector of (current_vertex, path_label_tuple)
        frontier = [(start, ())]
        len = 0
        while !isempty(frontier) && len < depth_bound
            len += 1
            next_frontier = Tuple[]
            for (cur, path) in frontier
                for (label, tgt) in out_edges[cur]
                    new_path = (path..., label)
                    m = (start, new_path)
                    push!(morphisms, m)
                    morphism_dom[m] = start
                    morphism_cod[m] = tgt
                    push!(next_frontier, (tgt, new_path))
                end
            end
            frontier = next_frontier
        end
    end

    morphisms_set = FinPolySet(morphisms)
    morphism_id_set = Set(morphisms)

    morphism_identity = Dict{Any,Any}(v => (v, ()) for v in verts)

    # Composition: concatenate paths whenever the composite is within depth.
    # In the truncated case, composites that would exceed `depth_bound` get
    # a *sentinel* entry (the source identity) so that the composition table
    # stays total — `from_category` builds a `Lens` whose `on_directions`
    # indexes this dict, and a missing key would crash `to_category` /
    # `validate_comonoid` rather than fail gracefully. The sentinel is
    # mathematically wrong (the real composite is a longer path), so
    # `validate_comonoid` reports the discrepancy as a category-laws
    # violation — which is exactly the structural manifestation of
    # "this isn't a valid free comonoid" the docstring promises.
    composition = Dict{Any,Any}()
    for f in morphisms
        for g in morphisms
            morphism_dom[g] == morphism_cod[f] || continue
            (vstart_f, path_f) = f
            (_,        path_g) = g
            composed = (vstart_f, (path_f..., path_g...))
            if composed in morphism_id_set
                composition[(f, g)] = composed
            else
                # Out-of-depth sentinel: the source identity at f's domain.
                # Categorically wrong; lets validation fail gracefully.
                composition[(f, g)] = morphism_identity[morphism_dom[f]]
            end
        end
    end

    cat = SmallCategory(FinPolySet(verts), morphisms_set,
                        morphism_dom, morphism_cod, morphism_identity, composition)
    from_category(cat)
end

# ============================================================
# Validation
# ============================================================

"""
    validate_category_laws(C::SmallCategory; verbose=false) -> Bool

Check the category axioms on a `SmallCategory`:

- Identity laws: `identity(dom(f)) ; f == f` and `f ; identity(cod(f)) == f`
  for every morphism `f`.
- Associativity: `(f ; g) ; h == f ; (g ; h)` for every composable triple.

Returns `true` if all axioms hold; with `verbose=true`, prints which axiom
failed (structural hint included). Composition direction is left-to-right:
`f ; g` means do `f` then `g`, so `cod(f) == dom(g)` is required.

For the structured result with per-failure detail (law symbol, location,
structural hint, actual / expected values), call
[`validate_category_laws_detailed`](@ref).
"""
validate_category_laws(C::SmallCategory; verbose::Union{Bool,Symbol}=false) =
    validate_category_laws_detailed(C; verbose=verbose).passed

"""
    validate_category_laws_detailed(C::SmallCategory; verbose=false) -> ValidationResult

Same checks as [`validate_category_laws`](@ref), but returns the full
`ValidationResult` with structural failure information. Use this when you
want to inspect `result.failures` programmatically.
"""
function validate_category_laws_detailed(C::SmallCategory; verbose::Union{Bool,Symbol}=false)
    failures = ValidationFailure[]
    collect_all = (verbose === :all)
    function record!(f::ValidationFailure)
        push!(failures, f)
        verbose === true && println("Category law violation: ", f.structural_hint)
        return collect_all
    end

    # Index morphisms by domain so we can iterate composable triples
    # directly rather than triple-looping over all morphisms (which would
    # be O(|morphisms|³)). With this index the associativity sweep is
    # O(Σ_{f,g,h composable} 1) — exactly the work we have to do.
    out_of = Dict{Any,Vector{Any}}()
    for o in C.objects.elements
        out_of[o] = Any[]
    end
    for f in C.morphisms.elements
        push!(out_of[C.dom[f]], f)
    end

    # Identity laws
    for f in C.morphisms.elements
        df, cf = C.dom[f], C.cod[f]
        id_d = C.identity[df]
        id_c = C.identity[cf]

        lhs = get(C.composition, (id_d, f), nothing)
        if lhs != f
            failure = ValidationFailure(
                :identity_left, (f,),
                "left identity at object $df: id_$df ; $f = $lhs, should be $f — " *
                "either identity[$df] is wrong or composition[(id_$df, $f)] is wrong",
                lhs, f)
            record!(failure) || return fail(failures)
        end

        rhs = get(C.composition, (f, id_c), nothing)
        if rhs != f
            failure = ValidationFailure(
                :identity_right, (f,),
                "right identity at object $cf: $f ; id_$cf = $rhs, should be $f — " *
                "either identity[$cf] is wrong or composition[($f, id_$cf)] is wrong",
                rhs, f)
            record!(failure) || return fail(failures)
        end
    end

    # Associativity
    for f in C.morphisms.elements
        for g in out_of[C.cod[f]]
            fg = C.composition[(f, g)]
            for h in out_of[C.cod[g]]
                gh = C.composition[(g, h)]
                lhs = C.composition[(fg, h)]
                rhs = C.composition[(f, gh)]
                if lhs != rhs
                    failure = ValidationFailure(
                        :associativity, (f, g, h),
                        "associativity fails at composable triple ($f, $g, $h): " *
                        "($f;$g);$h = $lhs but $f;($g;$h) = $rhs",
                        lhs, rhs)
                    record!(failure) || return fail(failures)
                end
            end
        end
    end

    isempty(failures) ? pass("category laws") : fail(failures)
end

"""
    validate_comonoid(c::Comonoid; mode=:category, verbose=false) -> Bool

Check that `c` really is a comonoid in `(Poly, y, ▷)`. Two equivalent
checking modes are supported:

- `mode = :category` (default) — translate to a `SmallCategory` via the
  Ahman–Uustalu correspondence and verify the category axioms (identity,
  associativity). By the equivalence `Comon(Poly, y, ▷) ≃ Cat#`, this is
  exactly the comonoid laws. Faster and more diagnostic when the failure
  is a category-axiom violation.

- `mode = :lens` — check the comonoid laws directly on the lens data,
  working position-by-position and direction-by-direction. The four
  laws (δ first-component, left counit, right counit, coassociativity)
  are spelled out below. Faster and more diagnostic when the failure
  is in raw lens data — and matches the form Niu/Spivak Chapter 7
  actually writes down.

Mathematically the two modes verify the same thing.

# `mode = :lens` — the four book laws

1. **δ acts as identity on the first position component.**
   For every `i ∈ c.positions`, `δ.on_positions(i) = (i, jbar_i)` for
   some `jbar_i : c[i] → c.positions`.

2. **Counit / left-identity law `(ε ▷ id) ∘ δ = id` (after the left
   unitor `λ : y ▷ c → c`).**
   - On positions: `jbar_i(id_i) = i`, where `id_i = ε♯_i(:pt)` is the
     identity direction at `i`.
   - On directions: for every direction `d ∈ c[i]`,
     `δ♯_i(id_i, d) = d`. (Composing `id_i` then `d` is `d`.)

3. **Counit / right-identity law `(id ▷ ε) ∘ δ = id` (after the right
   unitor `ρ : c ▷ y → c`).**
   - For every `i` and every `d ∈ c[i]`: let `j = jbar_i(d)` be the
     codomain of `d`. Then `δ♯_i(d, id_j) = d`. (Composing `d` then
     `id_j` is `d`.)

4. **Coassociativity `(δ ▷ id) ∘ δ = (id ▷ δ) ∘ δ` (after the
   associator).**
   - For every composable triple of directions `(a, b, e)` rooted at `i`
     — meaning `a ∈ c[i]`, `b ∈ c[jbar_i(a)]`, `e ∈ c[jbar_{j}(b)]` with
     `j = jbar_i(a)` — both bracketings agree:
     `δ♯_i(δ♯_i(a,b), e) = δ♯_i(a, δ♯_j(b, e))`.

The `:lens` mode avoids building the explicit unitor and associator
lenses by reading each law off element-wise.
"""
validate_comonoid(c::Comonoid; mode::Symbol=:category,
                  verbose::Union{Bool,Symbol}=false) =
    validate_comonoid_detailed(c; mode=mode, verbose=verbose).passed

"""
    validate_comonoid_detailed(c::Comonoid; mode=:category, verbose=false) -> ValidationResult

Same checks as [`validate_comonoid`](@ref), but returns the full
`ValidationResult` with structural failure information. Use this when you
want to inspect `result.failures` programmatically.
"""
function validate_comonoid_detailed(c::Comonoid; mode::Symbol=:category,
                                     verbose::Union{Bool,Symbol}=false)
    if mode === :category
        return validate_category_laws_detailed(to_category(c); verbose=verbose)
    elseif mode === :lens
        return _validate_comonoid_lens_form(c; verbose=verbose)
    else
        throw(ArgumentError("validate_comonoid: unknown mode $(repr(mode)); " *
                            "expected :category or :lens"))
    end
end

# Internal: the lens-form check, as Niu/Spivak Chapter 7 writes the laws.
# Reachable through `validate_comonoid(c; mode=:lens)`.
#
# Returns a `ValidationResult`. Each failure carries a structural hint
# naming the offending sub-component (duplicator on-positions, eraser on
# direction, etc.) rather than just a numbered law.
function _validate_comonoid_lens_form(c::Comonoid; verbose::Union{Bool,Symbol}=false)
    p = c.carrier
    pp = p.positions
    pp isa FinPolySet ||
        error("validate_comonoid mode=:lens requires finite carrier positions")

    failures = ValidationFailure[]
    collect_all = (verbose === :all)
    function record!(f::ValidationFailure)
        push!(failures, f)
        verbose === true && println("Law violation: ", f.structural_hint)
        return collect_all  # if collect_all, keep going; otherwise stop
    end

    # Cache δ.on_pos at each i and ε.on_dir at each i to avoid recomputing.
    jbar_at = Dict()
    id_at   = Dict()
    for i in pp.elements
        i′, jbar = c.duplicator.on_positions.f(i)
        if i′ != i
            f = ValidationFailure(
                :delta_first_component, (i,),
                "duplicator's on_positions at $i must preserve the position " *
                "component (return (i, jbar)); got first component $i′",
                i′, i)
            record!(f) || return fail(failures)
        end
        jbar_at[i] = jbar
        id_at[i]   = c.eraser.on_directions.f(i).f(:pt)
    end

    # --- Law 2: left counit ---
    for i in pp.elements
        Di = direction_at(p, i)::FinPolySet
        id_i = id_at[i]
        if jbar_at[i][id_i] != i
            f = ValidationFailure(
                :counit_left_positions, (i,),
                "duplicator's jbar at $i disagrees with eraser's identity choice: " *
                "jbar_$i(id_$i) = $(jbar_at[i][id_i]), should be $i",
                jbar_at[i][id_i], i)
            record!(f) || return fail(failures)
        end
        for d in Di.elements
            got = c.duplicator.on_directions.f(i).f((id_i, d))
            if got != d
                f = ValidationFailure(
                    :counit_left_directions, (i, d),
                    "δ♯_$i(id_$i, $d) should be $d (composing identity then $d), got $got — " *
                    "duplicator on-directions disagrees with eraser at object $i",
                    got, d)
                record!(f) || return fail(failures)
            end
        end
    end

    # --- Law 3: right counit ---
    for i in pp.elements
        Di = direction_at(p, i)::FinPolySet
        for d in Di.elements
            j = jbar_at[i][d]
            id_j = id_at[j]
            got = c.duplicator.on_directions.f(i).f((d, id_j))
            if got != d
                f = ValidationFailure(
                    :counit_right_directions, (i, d),
                    "δ♯_$i($d, id_$j) should be $d (composing $d then identity at codomain), got $got — " *
                    "duplicator on-directions disagrees with eraser at object $j",
                    got, d)
                record!(f) || return fail(failures)
            end
        end
    end

    # --- Law 4: coassociativity ---
    for i in pp.elements
        Di = direction_at(p, i)::FinPolySet
        for a in Di.elements
            j = jbar_at[i][a]
            Dj = direction_at(p, j)::FinPolySet
            for b in Dj.elements
                k = jbar_at[j][b]
                Dk = direction_at(p, k)::FinPolySet
                ab = c.duplicator.on_directions.f(i).f((a, b))
                for e in Dk.elements
                    be = c.duplicator.on_directions.f(j).f((b, e))
                    lhs = c.duplicator.on_directions.f(i).f((ab, e))
                    rhs = c.duplicator.on_directions.f(i).f((a, be))
                    if lhs != rhs
                        f = ValidationFailure(
                            :coassoc, (i, a, b),
                            "duplicator is not associative at composable triple ($i, $a, $b): " *
                            "($a;$b);$e = $lhs but $a;($b;$e) = $rhs — composition routing differs",
                            lhs, rhs)
                        record!(f) || return fail(failures)
                    end
                end
            end
        end
    end

    isempty(failures) ? pass("lens-form check") : fail(failures)
end

# ============================================================
# Built-in comonoids
# ============================================================

"""
    state_system_comonoid(S::PolySet) -> Comonoid

The state-system comonoid on `Sy^S`. Categorically: the *contractible
groupoid* on `S` (every pair of objects has a unique iso between them).

- Carrier: `state_system(S) = monomial(S, S) = Sy^S`.
- Eraser ε: at state `s`, identity is the direction equal to `s` (the
  "stay-put" arrow). This is exactly [`do_nothing_section`](@ref).
- Duplicator δ on positions: `s ↦ (s, id_S)` — the codomain of the
  arrow `(s, t)` is `t`.
- Duplicator δ on directions: `(a, b) ↦ b` — composing `s → t → u` gives
  `s → u`.
"""
function state_system_comonoid(S::PolySet)
    S isa FinPolySet ||
        error("state_system_comonoid requires finite S")
    carrier = state_system(S)
    eraser = do_nothing_section(S)

    dup_on_pos = s -> (s, Dict(t => t for t in S.elements))
    dup_on_dir = (s, ab) -> ab[2]
    # Use `subst_lazy` to avoid enumerating the substitution polynomial,
    # which has Σ_i |carrier(1)|^|carrier[i]| positions. With `Lens.cod`
    # widened to `AbstractPolynomial` and the `Comonoid` constructor's
    # cod-check going through `is_subst_of`, downstream consumption stays
    # lazy. Categorical-bridge `+`, `*`, `⊗` on `Comonoid` (which all go
    # through `from_category`) inherit the fix automatically.
    duplicator = Lens(carrier, subst_lazy(carrier, carrier),
                      dup_on_pos, dup_on_dir)

    Comonoid(carrier, eraser, duplicator)
end

"""
    discrete_comonoid(S::PolySet) -> Comonoid

The discrete-category comonoid on `Sy`. Categorically: the *discrete
category* on `S` — `|S|` objects, only identity morphisms.

- Carrier: `linear(S) = Sy`. Each position `s` has a single direction
  `:pt` (the identity at `s`).
- Eraser ε: trivially `:pt ↦ :pt` (only choice).
- Duplicator δ on positions: `s ↦ (s, :pt ↦ s)`. The unique morphism at
  `s` has codomain `s`.
- Duplicator δ on directions: `(:pt, :pt) ↦ :pt` — `id_s ; id_s = id_s`.
"""
function discrete_comonoid(S::PolySet)
    S isa FinPolySet ||
        error("discrete_comonoid requires finite S")
    carrier = linear(S)

    eraser = Lens(carrier, y, _ -> :pt, (_, _) -> :pt)

    dup_on_pos = s -> (s, Dict(:pt => s))
    dup_on_dir = (_, _ab) -> :pt
    # Use `subst_lazy` to avoid enumerating the substitution polynomial,
    # which has Σ_i |carrier(1)|^|carrier[i]| positions. With `Lens.cod`
    # widened to `AbstractPolynomial` and the `Comonoid` constructor's
    # cod-check going through `is_subst_of`, downstream consumption stays
    # lazy. Categorical-bridge `+`, `*`, `⊗` on `Comonoid` (which all go
    # through `from_category`) inherit the fix automatically.
    duplicator = Lens(carrier, subst_lazy(carrier, carrier),
                      dup_on_pos, dup_on_dir)

    Comonoid(carrier, eraser, duplicator)
end

"""
    monoid_comonoid(M::PolySet, e, op::Function) -> Comonoid

The one-object-category comonoid `BM` on a monoid `(M, e, op)`.
Categorically: a category with a single object whose morphisms form `M`.

- Carrier: `representable(M) = y^M`. One position `:pt`, direction-set `M`.
- Eraser ε: at `:pt`, identity direction is `e`.
- Duplicator δ on positions: `:pt ↦ (:pt, m ↦ :pt)` (only one object).
- Duplicator δ on directions: `(a, b) ↦ op(a, b)` (composition in `M`).

`op` is expected to be associative with `e` as identity; this is *not*
checked at construction. `validate_comonoid` will catch violations.
"""
function monoid_comonoid(M::PolySet, e, op::Function)
    M isa FinPolySet ||
        error("monoid_comonoid requires finite M")
    e in M.elements ||
        error("monoid_comonoid: identity $e is not in M = $M")

    carrier = representable(M)

    eraser = Lens(carrier, y, _ -> :pt, (_, _) -> e)

    dup_on_pos = _ -> (:pt, Dict(m => :pt for m in M.elements))
    dup_on_dir = (_, ab) -> op(ab[1], ab[2])
    # Use `subst_lazy` to avoid enumerating the substitution polynomial,
    # which has Σ_i |carrier(1)|^|carrier[i]| positions. With `Lens.cod`
    # widened to `AbstractPolynomial` and the `Comonoid` constructor's
    # cod-check going through `is_subst_of`, downstream consumption stays
    # lazy. Categorical-bridge `+`, `*`, `⊗` on `Comonoid` (which all go
    # through `from_category`) inherit the fix automatically.
    duplicator = Lens(carrier, subst_lazy(carrier, carrier),
                      dup_on_pos, dup_on_dir)

    Comonoid(carrier, eraser, duplicator)
end

# ============================================================
# Retrofunctors — morphisms of comonoids = functors
# ============================================================

"""
    Retrofunctor(dom::Comonoid, cod::Comonoid, underlying::Lens)

A *retrofunctor* from one comonoid to another: a `Lens` between the
underlying carriers that is also a comonoid morphism. Per Ahman–Uustalu,
these are exactly *functors* between the corresponding categories.

The functor laws (counit and comultiplication preservation) are *not*
verified at construction — call [`validate_retrofunctor`](@ref).
"""
struct Retrofunctor
    dom::Comonoid
    cod::Comonoid
    underlying::Lens
    function Retrofunctor(dom::Comonoid, cod::Comonoid, underlying::Lens)
        underlying.dom == dom.carrier ||
            error("Retrofunctor: underlying.dom ≠ dom.carrier")
        underlying.cod == cod.carrier ||
            error("Retrofunctor: underlying.cod ≠ cod.carrier")
        new(dom, cod, underlying)
    end
end

function show(io::IO, F::Retrofunctor)
    print(io, "Retrofunctor(")
    show(io, F.dom.carrier)
    print(io, " → ")
    show(io, F.cod.carrier)
    print(io, ")")
end

"""
    identity_retrofunctor(c::Comonoid) -> Retrofunctor

The identity retrofunctor `id_c : c → c`.
"""
identity_retrofunctor(c::Comonoid) =
    Retrofunctor(c, c, identity_lens(c.carrier))

"""
    compose(F::Retrofunctor, G::Retrofunctor) -> Retrofunctor

Compose two retrofunctors. `F : c → d`, `G : d → e` give `F ; G : c → e`.
"""
function compose(F::Retrofunctor, G::Retrofunctor)
    F.cod === G.dom || F.cod.carrier == G.dom.carrier ||
        error("Cannot compose retrofunctors: F.cod ≠ G.dom")
    Retrofunctor(F.dom, G.cod, compose(F.underlying, G.underlying))
end

"""
    validate_retrofunctor(F::Retrofunctor; strict=true, verbose=false) -> Bool

Check the comonoid-morphism axioms.

With `strict=true` (default), checks the laws as full lens equations:
- Counit preservation: `F ; ε_d == ε_c`.
- Comultiplication preservation: `F ; δ_d == δ_c ; (F ▷ F)`.

With `strict=false`, checks the same laws element-wise on positions and
directions. This is logically equivalent to `strict=true` (both check the
exact same axioms), just less reliant on `Lens ==`. Use `strict=false` if
you suspect a `Lens ==` brittleness is causing a false negative.

**Note:** neither mode passes on retrofunctors built by
[`cofree_universal`](@ref). The truncated cofree comonoid does not admit
a strict comonoid morphism from a comonoid with non-trivial walks; that's
a property of the truncation, not a `Lens ==` quirk. Verify the universal
property of `cofree_universal` directly via
`compose(F.underlying, cofree_unit(p, d))` versus the original labeling.

With `verbose=true`, prints which axiom failed first.
"""
validate_retrofunctor(F::Retrofunctor; strict::Bool=true,
                      verbose::Union{Bool,Symbol}=false) =
    validate_retrofunctor_detailed(F; strict=strict, verbose=verbose).passed

"""
    validate_retrofunctor_detailed(F::Retrofunctor; strict=true, verbose=false) -> ValidationResult

Same checks as [`validate_retrofunctor`](@ref), but returns the full
`ValidationResult` with structural failure information.
"""
function validate_retrofunctor_detailed(F::Retrofunctor; strict::Bool=true,
                                         verbose::Union{Bool,Symbol}=false)
    failures = ValidationFailure[]
    collect_all = (verbose === :all)
    function record!(f::ValidationFailure)
        push!(failures, f)
        verbose === true && println("Retrofunctor violation: ", f.structural_hint)
        return collect_all
    end

    if strict
        lhs1 = compose(F.underlying, F.cod.eraser)
        if lhs1 != F.dom.eraser
            failure = ValidationFailure(
                :counit_preservation, (),
                "F ⨟ ε_cod ≠ ε_dom — F.underlying composed with the cod-eraser does not equal the dom-eraser",
                lhs1, F.dom.eraser)
            record!(failure) || return fail(failures)
        end

        lhs2 = compose(F.underlying, F.cod.duplicator)
        rhs2 = compose(F.dom.duplicator, subst(F.underlying, F.underlying))
        if lhs2 != rhs2
            failure = ValidationFailure(
                :comult_preservation, (),
                "F ⨟ δ_cod ≠ δ_dom ⨟ (F ▷ F) — F.underlying does not preserve the duplicator strictly",
                lhs2, rhs2)
            record!(failure) || return fail(failures)
        end
        return isempty(failures) ? pass("retrofunctor (strict)") : fail(failures)
    end

    # --- Element-wise validation ---
    cdom = F.dom.carrier
    pp = cdom.positions
    pp isa FinPolySet ||
        error("validate_retrofunctor (non-strict) requires finite carrier positions")

    for i in pp.elements
        id_d_at_Fi = F.cod.eraser.on_directions.f(F.underlying.on_positions.f(i)).f(:pt)
        via_F = F.underlying.on_directions.f(i).f(id_d_at_Fi)
        id_c_at_i = F.dom.eraser.on_directions.f(i).f(:pt)
        if via_F != id_c_at_i
            failure = ValidationFailure(
                :counit_preservation_directions, (i,),
                "counit preservation at $i: F♯_$i pulls cod-identity at F($i) to $via_F, " *
                "but dom-identity at $i is $id_c_at_i — F.underlying's on-directions disagrees " *
                "with the comonoids' eraser identifications",
                via_F, id_c_at_i)
            record!(failure) || return fail(failures)
        end
    end

    for i in pp.elements
        Fi = F.underlying.on_positions.f(i)
        Di_d = direction_at(F.cod.carrier, Fi)::FinPolySet
        Fi_dup = F.cod.duplicator.on_positions.f(Fi)
        jbar_d = Fi_dup[2]
        for a in Di_d.elements
            j_d = jbar_d[a]
            Dj_d = direction_at(F.cod.carrier, j_d)::FinPolySet
            for b in Dj_d.elements
                composed_d = F.cod.duplicator.on_directions.f(Fi).f((a, b))
                lhs = F.underlying.on_directions.f(i).f(composed_d)
                a_in_dom = F.underlying.on_directions.f(i).f(a)
                j_in_dom = F.dom.duplicator.on_positions.f(i)[2][a_in_dom]
                F_j_in_dom = F.underlying.on_positions.f(j_in_dom)
                if F_j_in_dom != j_d
                    failure = ValidationFailure(
                        :comult_positions, (i, a),
                        "comult preservation at ($i, $a): counit-preservation contradiction — " *
                        "F($j_in_dom) = $F_j_in_dom should equal cod-codomain $j_d",
                        F_j_in_dom, j_d)
                    record!(failure) || return fail(failures)
                    continue
                end
                b_in_dom = F.underlying.on_directions.f(j_in_dom).f(b)
                rhs = F.dom.duplicator.on_directions.f(i).f((a_in_dom, b_in_dom))
                if lhs != rhs
                    failure = ValidationFailure(
                        :comult_directions, (i, a, b),
                        "comult preservation at ($i, $a, $b): F♯ ∘ δ_cod gives $lhs " *
                        "but δ_dom ∘ (F♯, F♯) gives $rhs — direction-routing diverges",
                        lhs, rhs)
                    record!(failure) || return fail(failures)
                end
            end
        end
    end

    isempty(failures) ? pass("retrofunctor (element-wise)") : fail(failures)
end

# ============================================================
# comonoid_from_data (Extensions v2 PR #5)
# ============================================================
#
# Authoring helper: build a `Comonoid` from explicit Dicts of
# eraser / duplicator data, without hand-building the underlying
# `Lens` objects. Mirrors the bicomodule_from_data API. Validates the
# result by default; pass `validate=false` to skip (Q5.2).

"""
    comonoid_from_data(
        carrier::Polynomial;
        eraser_table::AbstractDict,            # pos -> identity_direction at pos
        duplicator_emit::AbstractDict,         # (pos, dir) -> next_pos
        duplicator_compose::AbstractDict,      # (pos, dir1, dir2) -> composed_dir
        validate::Bool=true,
    ) -> Comonoid

Build a `Comonoid` from authored data tables, constructing the eraser
and duplicator lenses internally.

  - `eraser_table[pos]` is the identity direction at `pos` (the result of
    the eraser's on_directions when given a `:pt` y-direction).
  - `duplicator_emit[(pos, dir)]` is the codomain of the morphism `dir` at
    `pos` — the `jbar` value the duplicator's on_positions returns.
  - `duplicator_compose[(pos, dir1, dir2)]` is the composed direction
    `dir1 ; dir2` viewed at `pos` — the result of the duplicator's
    on_directions on the pair.

When `validate=true` (default), the result is run through
[`validate_comonoid`](@ref); failure raises an `ArgumentError` with the
underlying validation summary so authoring mistakes surface immediately.
Pass `validate=false` for intermediate constructions you'll validate
later.
"""
function comonoid_from_data(carrier::Polynomial;
                            eraser_table::AbstractDict,
                            duplicator_emit::AbstractDict,
                            duplicator_compose::AbstractDict,
                            validate::Bool=true)
    eraser = Lens(carrier, y,
                  _ -> :pt,
                  (i, _) -> eraser_table[i])

    dup_on_pos = i -> begin
        Di = direction_at(carrier, i)::FinPolySet
        jbar = Dict(a => duplicator_emit[(i, a)] for a in Di.elements)
        (i, jbar)
    end
    dup_on_dir = (i, ab) -> begin
        a, b = ab
        duplicator_compose[(i, a, b)]
    end

    duplicator = Lens(carrier, subst_lazy(carrier, carrier),
                      dup_on_pos, dup_on_dir)

    result = Comonoid(carrier, eraser, duplicator)

    if validate
        r = validate_comonoid_detailed(result)
        r.passed || throw(ArgumentError(
            "comonoid_from_data: validation failed — " * r.summary *
            "; pass `validate=false` to skip."))
    end
    result
end
