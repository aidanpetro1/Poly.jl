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
        cc = subst(carrier, carrier)
        duplicator.cod == cc ||
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

    duplicator = Lens(carrier, subst(carrier, carrier),
                      dup_on_pos, dup_on_dir)

    Comonoid(carrier, eraser, duplicator)
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
failed first. Composition direction is left-to-right: `f ; g` means do `f`
then `g`, so `cod(f) == dom(g)` is required.
"""
function validate_category_laws(C::SmallCategory; verbose::Bool=false)
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
            verbose && println("Left identity failed: id(dom($f)) ; $f = $lhs ≠ $f")
            return false
        end

        rhs = get(C.composition, (f, id_c), nothing)
        if rhs != f
            verbose && println("Right identity failed: $f ; id(cod($f)) = $rhs ≠ $f")
            return false
        end
    end

    # Associativity: enumerate composable triples (f, g, h) directly via
    # the dom-index. For each f, g ranges over morphisms out of cod(f),
    # and h ranges over morphisms out of cod(g).
    for f in C.morphisms.elements
        for g in out_of[C.cod[f]]
            fg = C.composition[(f, g)]
            for h in out_of[C.cod[g]]
                gh = C.composition[(g, h)]
                lhs = C.composition[(fg, h)]
                rhs = C.composition[(f, gh)]
                if lhs != rhs
                    verbose && println("Associativity failed for ($f, $g, $h): ($f;$g);$h = $lhs but $f;($g;$h) = $rhs")
                    return false
                end
            end
        end
    end

    true
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
function validate_comonoid(c::Comonoid; mode::Symbol=:category, verbose::Bool=false)
    if mode === :category
        return validate_category_laws(to_category(c); verbose=verbose)
    elseif mode === :lens
        return _validate_comonoid_lens_form(c; verbose=verbose)
    else
        throw(ArgumentError("validate_comonoid: unknown mode $(repr(mode)); " *
                            "expected :category or :lens"))
    end
end

# Internal: the lens-form check, as Niu/Spivak Chapter 7 writes the laws.
# Reachable through `validate_comonoid(c; mode=:lens)`.
function _validate_comonoid_lens_form(c::Comonoid; verbose::Bool=false)
    p = c.carrier
    pp = p.positions
    pp isa FinPolySet ||
        error("validate_comonoid mode=:lens requires finite carrier positions")

    # Cache δ.on_pos at each i and ε.on_dir at each i to avoid recomputing.
    jbar_at = Dict()
    id_at   = Dict()
    for i in pp.elements
        i′, jbar = c.duplicator.on_positions.f(i)
        if i′ != i
            verbose && println("Law 1 (δ first-component) failed at $i: got $i′")
            return false
        end
        jbar_at[i] = jbar
        id_at[i]   = c.eraser.on_directions.f(i).f(:pt)
    end

    # --- Law 2: left counit ---
    for i in pp.elements
        Di = direction_at(p, i)::FinPolySet
        id_i = id_at[i]
        # On positions: jbar_i(id_i) == i
        if jbar_at[i][id_i] != i
            verbose && println("Law 2 (left counit, positions) failed at $i: jbar_i(id_$i) = $(jbar_at[i][id_i]) ≠ $i")
            return false
        end
        # On directions: δ♯_i(id_i, d) == d for every d ∈ c[i]
        for d in Di.elements
            got = c.duplicator.on_directions.f(i).f((id_i, d))
            if got != d
                verbose && println("Law 2 (left counit, directions) failed at ($i, $d): δ♯ = $got ≠ $d")
                return false
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
                verbose && println("Law 3 (right counit) failed at ($i, $d): δ♯ = $got ≠ $d")
                return false
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
                        verbose && println("Law 4 (coassoc) failed at ($i, $a, $b, $e): ($a;$b);$e = $lhs vs $a;($b;$e) = $rhs")
                        return false
                    end
                end
            end
        end
    end

    true
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
    duplicator = Lens(carrier, subst(carrier, carrier),
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
    duplicator = Lens(carrier, subst(carrier, carrier),
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
    duplicator = Lens(carrier, subst(carrier, carrier),
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
function validate_retrofunctor(F::Retrofunctor; strict::Bool=true, verbose::Bool=false)
    if strict
        lhs1 = compose(F.underlying, F.cod.eraser)
        if lhs1 != F.dom.eraser
            verbose && println("Counit preservation failed: F ⨟ ε_d ≠ ε_c")
            return false
        end

        lhs2 = compose(F.underlying, F.cod.duplicator)
        rhs2 = compose(F.dom.duplicator, subst(F.underlying, F.underlying))
        if lhs2 != rhs2
            verbose && println("Comultiplication preservation failed: F ⨟ δ_d ≠ δ_c ⨟ (F ▷ F)")
            return false
        end
        return true
    end

    # --- Element-wise validation ---
    cdom = F.dom.carrier
    pp = cdom.positions
    pp isa FinPolySet ||
        error("validate_retrofunctor (non-strict) requires finite carrier positions")

    # Counit preservation, on positions: F.cod.eraser ∘ F = F.dom.eraser
    # Both sides on positions send every i to :pt — trivially true.
    # On directions at i: ε_d♯_{F(i)}(:pt) walked back through F♯_i should
    # equal ε_c♯_i(:pt) — i.e., the identity direction at i in the dom comonoid.
    for i in pp.elements
        id_d_at_Fi = F.cod.eraser.on_directions.f(F.underlying.on_positions.f(i)).f(:pt)
        via_F = F.underlying.on_directions.f(i).f(id_d_at_Fi)
        id_c_at_i = F.dom.eraser.on_directions.f(i).f(:pt)
        if via_F != id_c_at_i
            verbose && println("Counit preservation (directions) failed at $i: $via_F ≠ $id_c_at_i")
            return false
        end
    end

    # Comultiplication preservation, on directions: for every (a, b) ∈ (c_d ▷ c_d)
    # at F(i), the two ways of pulling back to a c_dom-direction at i agree.
    # LHS: F♯_i applied to δ_d♯_{F(i)}((a, b))
    # RHS: δ_dom♯_i applied to (F♯_i(a), F♯_{j}(b)) where j is the c_dom-codomain.
    for i in pp.elements
        Fi = F.underlying.on_positions.f(i)
        Di_d = direction_at(F.cod.carrier, Fi)::FinPolySet
        # Iterate over (c_d ▷ c_d)-directions at δ_d(Fi).
        # δ_d(Fi) = (Fi, jbar_d) — a position of c_d ▷ c_d. Direction-set is
        # pairs (a, b) with a ∈ c_d[Fi], b ∈ c_d[jbar_d(a)].
        Fi_dup = F.cod.duplicator.on_positions.f(Fi)
        jbar_d = Fi_dup[2]
        for a in Di_d.elements
            j_d = jbar_d[a]
            Dj_d = direction_at(F.cod.carrier, j_d)::FinPolySet
            for b in Dj_d.elements
                # LHS: F♯_i(δ_d♯_{Fi}(a, b))
                composed_d = F.cod.duplicator.on_directions.f(Fi).f((a, b))
                lhs = F.underlying.on_directions.f(i).f(composed_d)
                # RHS: δ_dom♯_i(F♯_i(a), F♯_j(b)) where j = c_dom-codomain after F♯_i(a).
                a_in_dom = F.underlying.on_directions.f(i).f(a)
                j_in_dom = F.dom.duplicator.on_positions.f(i)[2][a_in_dom]
                # F.underlying.on_pos(j_in_dom) should give some position of c_d
                # which we can use to call F.underlying.on_directions at j_in_dom
                # with input b. But b is a c_d-direction at j_d, not at F(j_in_dom).
                # The key bridge is: by counit-preservation-on-positions, the
                # c_d-position visited from Fi via a equals F(j_in_dom).
                F_j_in_dom = F.underlying.on_positions.f(j_in_dom)
                if F_j_in_dom != j_d
                    verbose && println("Comult (positions) failed at ($i, $a): F($j_in_dom) = $F_j_in_dom ≠ $j_d (counit-preservation contradiction)")
                    return false
                end
                # b is in c_d[F(j_in_dom)] = c_d[j_d], so we can pull it back via F♯ at j_in_dom.
                b_in_dom = F.underlying.on_directions.f(j_in_dom).f(b)
                rhs = F.dom.duplicator.on_directions.f(i).f((a_in_dom, b_in_dom))
                if lhs != rhs
                    verbose && println("Comult preservation (directions) failed at ($i, $a, $b): $lhs ≠ $rhs")
                    return false
                end
            end
        end
    end

    return true
end
