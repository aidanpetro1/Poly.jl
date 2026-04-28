# ============================================================
# Cofree comonoid T_p (Sprint 8 — Niu/Spivak Chapter 8)
# ============================================================
#
# The cofree comonoid `T_p` on a polynomial `p` is the terminal coalgebra
# for the functor `X ↦ p ▷ X` in (Poly, y, ▷). Its positions are
# *p-behaviors* — trees where each non-leaf node is labeled by a position
# `i ∈ p(1)` and has children indexed by `p[i]`. Its directions at a tree
# `t` are paths through `t`, with codomain "subtree at end of path."
# Composition of paths is concatenation; identity is the empty path.
#
# Categorically: `T_p` presents the *path category* of the (typically
# infinite) tree of all `p`-behaviors.
#
# `T_p` itself is infinite. We provide `cofree_comonoid(p, depth)`, the
# *depth-bounded* truncation `T_p^{(d)}`. Its carrier includes all
# `p`-trees of depth ≤ d. Walks of length `k ≤ m` through a depth-`m`
# tree land on depth-`(m-k)` trees, which are still in the carrier — so
# the comonoid laws hold exactly on the truncation, not merely up to iso.
#
# Combinatorial caveat: the number of `p`-trees of depth ≤ d grows like
# a tower of exponentials in `d`. Useful for `d` ∈ {1, 2, 3} with small
# `p`; demos and tests stay in that range.

# ============================================================
# BehaviorTree — a single p-behavior
# ============================================================

"""
    BehaviorTree(label, children)

A `p`-behavior: a node labeled `label ∈ p(1)` with `children` a `Dict`
keyed by `p[label]`. A leaf is a `BehaviorTree` with empty `children`
(either because the position has empty direction-set, or because the
tree was truncated at depth 0).

Two `BehaviorTree`s are `==` iff their labels and children dicts agree
recursively.
"""
struct BehaviorTree
    label::Any
    children::Dict{Any,BehaviorTree}
end

function ==(a::BehaviorTree, b::BehaviorTree)
    a.label == b.label || return false
    a.children == b.children
end

function hash(t::BehaviorTree, h::UInt)
    h = hash(:BehaviorTree, h)
    h = hash(t.label, h)
    hash(t.children, h)
end

function show(io::IO, t::BehaviorTree)
    if isempty(t.children)
        print(io, "•", t.label)
    else
        print(io, "•", t.label, "[")
        first = true
        # Sort keys by string representation for stable display.
        ks = sort(collect(keys(t.children)); by=string)
        for k in ks
            first || print(io, ", ")
            first = false
            print(io, k, "↦")
            show(io, t.children[k])
        end
        print(io, "]")
    end
end

# ============================================================
# Tree enumeration
# ============================================================

# Internal: trees of *exactly* depth d. For a position with empty
# direction-set, the only valid tree is a leaf — depth is 0 regardless.
function _trees_at_depth(p::Polynomial, d::Int)
    p.positions isa FinPolySet ||
        error("_trees_at_depth requires finite positions")

    if d == 0
        return [BehaviorTree(i, Dict{Any,BehaviorTree}())
                for i in p.positions.elements]
    end

    sub = _trees_at_depth(p, d - 1)
    out = BehaviorTree[]
    for i in p.positions.elements
        Di = direction_at(p, i)
        Di isa FinPolySet ||
            error("_trees_at_depth: p[$i] is $(typeof(Di)); need FinPolySet")
        if isempty(Di.elements)
            push!(out, BehaviorTree(i, Dict{Any,BehaviorTree}()))
        else
            for choice in Iterators.product((sub for _ in Di.elements)...)
                children = Dict{Any,BehaviorTree}(zip(Di.elements, choice))
                push!(out, BehaviorTree(i, children))
            end
        end
    end
    out
end

"""
    behavior_trees(p::Polynomial, depth::Int) -> Vector{BehaviorTree}

All `p`-behaviors of depth ≤ `depth`, deduplicated. The carrier of
[`cofree_comonoid`](@ref)`(p, depth)` is `FinPolySet` of these.

Grows fast — see the file header for combinatorial bounds.
"""
function behavior_trees(p::Polynomial, depth::Int)
    depth ≥ 0 || throw(ArgumentError("depth must be ≥ 0; got $depth"))
    out = BehaviorTree[]
    seen = Set{BehaviorTree}()
    for k in 0:depth
        for t in _trees_at_depth(p, k)
            if !(t in seen)
                push!(seen, t)
                push!(out, t)
            end
        end
    end
    out
end

# ============================================================
# Paths and walks
# ============================================================

"""
    tree_paths(t::BehaviorTree) -> Vector{Tuple}

All paths from the root through `t`, encoded as tuples of directions.
Includes the empty path `()` (the identity at `t`). For a depth-m tree,
paths range from length 0 to m.
"""
function tree_paths(t::BehaviorTree)
    out = Tuple[()]
    # Sort children keys for deterministic ordering across runs.
    ks = sort(collect(keys(t.children)); by=string)
    for dir in ks
        sub = t.children[dir]
        for π in tree_paths(sub)
            push!(out, (dir, π...))
        end
    end
    out
end

"""
    tree_walk(t::BehaviorTree, π) -> BehaviorTree

The destination of path `π` (a tuple of directions) starting at `t`.
Errors if any step is not actually a child of the current node.
"""
function tree_walk(t::BehaviorTree, π)
    isempty(π) && return t
    return tree_walk(t.children[π[1]], π[2:end])
end

# ============================================================
# cofree_comonoid — the depth-bounded T_p^{(d)}
# ============================================================

"""
    cofree_comonoid(p::Polynomial, depth::Int) -> Comonoid

The depth-`d` truncation of the cofree comonoid `T_p` on `p`.

- Carrier: positions are all `p`-behaviors of depth ≤ `depth`; the
  direction-set at a tree `t` is `tree_paths(t)`.
- Eraser ε: at every tree, the identity direction is the empty path `()`.
- Duplicator δ: at a tree `t`, on positions sends `t ↦ (t, jbar_t)` with
  `jbar_t(π) = tree_walk(t, π)`. On directions, concatenates paths:
  `(π_a, π_b) ↦ (π_a..., π_b...)`.

By Niu/Spivak Chapter 8, the (full, infinite) `T_p` is the cofree
comonoid on `p` in `(Poly, y, ▷)`. The truncation here is exact on the
data we keep — every comonoid law verifies via [`validate_comonoid`](@ref).

Use small `depth` (1–3) for non-trivial `p`; tree counts grow like a
tower of exponentials.
"""
function cofree_comonoid(p::Polynomial, depth::Int)
    p.positions isa FinPolySet ||
        error("cofree_comonoid requires finite p.positions")
    depth ≥ 0 || throw(ArgumentError("depth must be ≥ 0; got $depth"))

    trees = behavior_trees(p, depth)
    trees_set = FinPolySet(trees)

    dir_at = t -> FinPolySet(tree_paths(t))
    carrier = Polynomial(trees_set, dir_at)

    eraser = Lens(carrier, y, _ -> :pt, (_, _) -> ())

    dup_on_pos = t -> begin
        Di = direction_at(carrier, t)::FinPolySet
        jbar = Dict{Any,BehaviorTree}(π => tree_walk(t, π) for π in Di.elements)
        (t, jbar)
    end
    dup_on_dir = (_, π_pair) -> begin
        π_a, π_b = π_pair
        return (π_a..., π_b...)
    end

    duplicator = Lens(carrier, subst(carrier, carrier),
                      dup_on_pos, dup_on_dir)

    Comonoid(carrier, eraser, duplicator)
end

# ============================================================
# Comodules — first cut
# ============================================================
#
# A right c-comodule is a polynomial X with a coaction λ : X → X ▷ c
# satisfying counit and coassociativity. The regular comodule is c
# itself with coaction = δ.
#
# We provide the struct, the regular-comodule constructor, and a
# counit-law validator (the simpler of the two laws). Coassociativity
# requires unitor/associator infrastructure for full lens-equation
# checking; we validate it pointwise on positions and directions.

"""
    RightComodule(carrier::Polynomial, base::Comonoid, coaction::Lens)

A right comodule over `base`. The constructor type-checks that
`coaction : carrier → carrier ▷ base.carrier`. The comodule laws
(counit, coassociativity) are not checked at construction —
use [`validate_right_comodule`](@ref).

Niu/Spivak Chapter 8: a right c-comodule structure on `X` is the same
data as a *prafunctor* `1 → cat(c)`, where `cat(c)` is the category
presented by `c`. (Bicomodules generalize this to functors between
categories.)
"""
struct RightComodule
    carrier::Polynomial
    base::Comonoid
    coaction::Lens
    function RightComodule(carrier::Polynomial, base::Comonoid, coaction::Lens)
        coaction.dom == carrier ||
            error("RightComodule: coaction.dom ≠ carrier")
        expected_cod = subst(carrier, base.carrier)
        coaction.cod == expected_cod ||
            error("RightComodule: coaction.cod ≠ carrier ▷ base.carrier")
        new(carrier, base, coaction)
    end
end

function show(io::IO, M::RightComodule)
    print(io, "RightComodule(")
    show(io, M.carrier)
    print(io, " over ")
    show(io, M.base.carrier)
    print(io, ")")
end

"""
    regular_right_comodule(c::Comonoid) -> RightComodule

The regular right comodule on `c`: `c.carrier` with `c.duplicator` as
the coaction `c → c ▷ c`. The coaction laws fall out of `c`'s comonoid
laws — `validate_right_comodule(regular_right_comodule(c))` returns `true` iff `c`
satisfies its comonoid laws.
"""
regular_right_comodule(c::Comonoid) = RightComodule(c.carrier, c, c.duplicator)

"""
    validate_right_comodule(M::RightComodule; verbose=false) -> Bool

Check the right-comodule axioms on `M.coaction` element-wise:

1. **First-component law** (counit, on positions):
   for every `x ∈ X(1)`, `coaction.on_positions(x) = (x, mbar_x)` for
   some `mbar_x : X[x] → c(1)`. (The first projection acts as the
   identity.)

2. **Counit law** (on directions): for every `x ∈ X(1)` and every
   `a ∈ X[x]`, `coaction♯_x(a, id_{c at mbar_x(a)}) = a`. (Pairing an
   `X`-direction with the identity at its tracked `c`-position recovers
   the direction.)

3. **Coassociativity law**: for every composable triple `(x, a, b)` with
   `a ∈ X[x]` and `b ∈ c[mbar_x(a)]`, the two ways of factoring
   "step in X then two steps in c" agree:

       δ_c♯_{mbar_x(a)}(b1, b2) iterated against coaction matches
       coaction's own iteration.

   Concretely we check that both bracketings of a length-3 trip yield the
   same X-direction, mirroring the comonoid coassoc check.
"""
function validate_right_comodule(M::RightComodule; verbose::Bool=false)
    X = M.carrier
    c = M.base.carrier
    λ = M.coaction
    pp = X.positions
    pp isa FinPolySet ||
        error("validate_right_comodule requires finite X.positions")

    # Cache λ.on_positions outputs and identity directions on the base.
    mbar_at = Dict()
    id_in_c = Dict()
    for x in pp.elements
        x′, mbar = λ.on_positions.f(x)
        if x′ != x
            verbose && println("Law 1 (first-component) failed at $x: λ_1 = ($x′, _) ≠ ($x, _)")
            return false
        end
        mbar_at[x] = mbar
    end
    for j in c.positions.elements
        id_in_c[j] = M.base.eraser.on_directions.f(j).f(:pt)
    end

    # Law 2: counit on directions.
    for x in pp.elements
        Dx = direction_at(X, x)::FinPolySet
        for a in Dx.elements
            j = mbar_at[x][a]
            id_j = id_in_c[j]
            got = λ.on_directions.f(x).f((a, id_j))
            if got != a
                verbose && println("Law 2 (counit, directions) failed at ($x, $a): λ♯ = $got ≠ $a")
                return false
            end
        end
    end

    # Law 3: coassoc — for every (x, a, b1, b2) with the right shapes,
    # check that "step in X by a, then split in c via δ_c" matches in
    # both bracketings. The check is structurally identical to the
    # comonoid coassoc check, applied to λ.on_directions and
    # M.base.duplicator.on_directions.
    for x in pp.elements
        Dx = direction_at(X, x)::FinPolySet
        mbar_x = mbar_at[x]
        for a in Dx.elements
            j = mbar_x[a]
            Dj_in_c = direction_at(c, j)::FinPolySet
            for b1 in Dj_in_c.elements
                # Compose b1 onto a via λ to get a new X-direction
                a′ = λ.on_directions.f(x).f((a, b1))
                # That new direction is in X[x] (by counit on directions
                # we know it's a regular X-direction). Its tracked
                # c-position via mbar_x is some k.
                k = M.base.duplicator.on_positions.f(j)[2][b1]
                # δ_c on positions: j ↦ (j, jbar_j); jbar_j(b1) = k.
                Dk_in_c = direction_at(c, k)::FinPolySet
                for b2 in Dk_in_c.elements
                    # LHS bracket: ((a, b1), b2) → step a-then-b1 in λ,
                    # then a single c-step b2.
                    lhs = λ.on_directions.f(x).f((a′, b2))
                    # RHS bracket: (a, (b1, b2)) → first compose (b1, b2)
                    # in c via δ_c♯, then step in λ.
                    b1b2 = M.base.duplicator.on_directions.f(j).f((b1, b2))
                    rhs = λ.on_directions.f(x).f((a, b1b2))
                    if lhs != rhs
                        verbose && println("Law 3 (coassoc) failed at ($x, $a, $b1, $b2): $lhs ≠ $rhs")
                        return false
                    end
                end
            end
        end
    end

    true
end

# ============================================================
# Cofree universal property: unit lens and the unique factoring
# ============================================================

"""
    cofree_unit(p::Polynomial, depth::Int) -> Lens

The unit (or "labeling") lens `ε_p^{(d)} : T_p^{(d)} → p` of the cofree
comonoid. On positions, sends a tree to its root label. On directions
at a tree `t`, sends a `p`-direction `a ∈ p[label(t)]` to the singleton
path `(a,)`.

**Caveat:** `(a,)` is a valid `T_p`-direction at `t` iff `t` has children
expanded (i.e., it isn't a depth-0 stub). The carrier of
[`cofree_comonoid`](@ref)`(p, depth)` includes depth-0 trees for every
position, so the lens's on-directions function may return values that
aren't in the codomain set for those positions. In practice, evaluate
`cofree_unit` only at trees of positive depth, or at positions whose
direction-set is empty.

Together with [`cofree_universal`](@ref), this characterizes `T_p` as the
cofree comonoid: every comonoid `c` with a labeling `c → p` factors
uniquely through `T_p` so that the factoring composed with `cofree_unit`
is the original labeling.
"""
function cofree_unit(p::Polynomial, depth::Int)
    depth ≥ 1 ||
        throw(ArgumentError("cofree_unit needs depth ≥ 1; got $depth"))

    Tp = cofree_comonoid(p, depth)

    on_pos = t -> t.label
    on_dir = (_t, a) -> (a,)

    Lens(Tp.carrier, p, on_pos, on_dir)
end

# Walk a `p`-path through `c` starting at position `i`, lifting through the
# labeling and folding via δ_c, to recover a single `c`-direction at `i`.
# Used by cofree_universal to define the underlying lens on directions.
function _path_to_c_direction(c::Comonoid, labeling::Lens, i, π)
    if isempty(π)
        return c.eraser.on_directions.f(i).f(:pt)
    end
    a = π[1]
    rest = Base.tail(π)
    d_first = labeling.on_directions.f(i).f(a)
    if isempty(rest)
        return d_first
    end
    j = c.duplicator.on_positions.f(i)[2][d_first]
    d_rest = _path_to_c_direction(c, labeling, j, rest)
    return c.duplicator.on_directions.f(i).f((d_first, d_rest))
end

# Recursively build the depth-`d` p-tree at the c-position `i` under
# `labeling`, walking c via `c.duplicator` to discover codomains.
function _tree_for_position(c::Comonoid, labeling::Lens, p::Polynomial, i, d::Int)
    a_pos = labeling.on_positions.f(i)
    if d == 0
        return BehaviorTree(a_pos, Dict{Any,BehaviorTree}())
    end
    Da = direction_at(p, a_pos)
    Da isa FinPolySet ||
        error("_tree_for_position: p[$a_pos] is $(typeof(Da)); need FinPolySet")
    if isempty(Da.elements)
        return BehaviorTree(a_pos, Dict{Any,BehaviorTree}())
    end
    children = Dict{Any,BehaviorTree}()
    for a in Da.elements
        d_in_c = labeling.on_directions.f(i).f(a)
        j = c.duplicator.on_positions.f(i)[2][d_in_c]
        children[a] = _tree_for_position(c, labeling, p, j, d - 1)
    end
    return BehaviorTree(a_pos, children)
end

"""
    cofree_universal(c::Comonoid, labeling::Lens, depth::Int) -> Retrofunctor

Given a comonoid `c` and a labeling lens `labeling : c.carrier → p`,
build the unique retrofunctor `c → T_p^{(d)}` factoring the labeling
through the cofree comonoid. By Niu/Spivak Chapter 8, this is the
universal property of `T_p`:

- `cofree_universal(c, labeling, d).underlying ⨟ cofree_unit(p, d) == labeling`
- and the retrofunctor is unique with that property (up to the depth
  bound).

Concretely: each `c`-position `i` is sent to the depth-`d` p-tree
obtained by repeatedly stepping in `c` (via `c.duplicator`) under the
labels supplied by `labeling`. Each `c`-direction is sent to the
corresponding `T_p`-path.

# Caveat: truncation breaks the strict comult law

The full (infinite) `T_p` *is* the cofree comonoid, so the retrofunctor
this function builds satisfies the strict comonoid-morphism laws there.
Under depth-`d` truncation those laws fail in general: walking `k ≤ d`
steps in `T_p^{(d)}` from `F(i)` lands on a depth-`(d-k)` tree, while
`c.duplicator ⨟ (F ▷ F)` lands on a fresh depth-`d` tree at the
c-codomain — different objects in the truncated carrier. So
`validate_retrofunctor` will return `false` whenever `c` has non-trivial
walks (e.g. a state-system comonoid).

The element-wise universal property still holds:
`F.underlying ⨟ cofree_unit(p, d) ≡ labeling` pointwise on positions and
directions. That's the substantive content. To verify, compose the
underlying lens with `cofree_unit(p, d)` and compare to `labeling`
position-by-position and direction-by-direction; do not call
`validate_retrofunctor(F)` (in either mode), as that asserts the strict
comonoid-morphism laws which fail under truncation regardless of how
they're checked.
"""
function cofree_universal(c::Comonoid, labeling::Lens, depth::Int)
    labeling.dom == c.carrier ||
        error("cofree_universal: labeling.dom ≠ c.carrier")
    p = labeling.cod
    p.positions isa FinPolySet ||
        error("cofree_universal: labeling.cod must have FinPolySet positions")

    Tp = cofree_comonoid(p, depth)

    F_on_pos = i -> _tree_for_position(c, labeling, p, i, depth)
    F_on_dir = (i, π) -> _path_to_c_direction(c, labeling, i, π)

    underlying = Lens(c.carrier, Tp.carrier, F_on_pos, F_on_dir)
    Retrofunctor(c, Tp, underlying)
end

# ============================================================
# ============================================================
# Left comodules
# ============================================================
#
# A LEFT c-comodule is a polynomial X with a coaction `λ : X → c ▷ X`
# satisfying counit and coassociativity:
#
#   (ε_c ▷ id_X) ∘ λ  =  λ_left_unitor   (counit)
#   (δ_c ▷ id_X) ∘ λ  =  (id_c ▷ λ) ∘ λ  (coassoc, modulo associator)
#
# Mirror image of [`RightComodule`](@ref) (right comodules). Together with
# right comodules, left comodules form the two halves of a [`Bicomodule`](@ref).

"""
    LeftComodule(carrier::Polynomial, base::Comonoid, coaction::Lens)

A left comodule over `base`. The constructor type-checks that
`coaction : carrier → base.carrier ▷ carrier`. RightComodule laws (counit,
coassociativity) are not checked at construction —
use [`validate_left_comodule`](@ref).
"""
struct LeftComodule
    carrier::Polynomial
    base::Comonoid
    coaction::Lens
    function LeftComodule(carrier::Polynomial, base::Comonoid, coaction::Lens)
        coaction.dom == carrier ||
            error("LeftComodule: coaction.dom ≠ carrier")
        expected_cod = subst(base.carrier, carrier)
        coaction.cod == expected_cod ||
            error("LeftComodule: coaction.cod ≠ base.carrier ▷ carrier")
        new(carrier, base, coaction)
    end
end

function show(io::IO, M::LeftComodule)
    print(io, "LeftComodule(")
    show(io, M.base.carrier)
    print(io, " ▷ ")
    show(io, M.carrier)
    print(io, ")")
end

"""
    regular_left_comodule(c::Comonoid) -> LeftComodule

The regular left comodule on `c`: `c.carrier` with `c.duplicator` as the
coaction. Validates iff `c` itself is a valid comonoid.
"""
regular_left_comodule(c::Comonoid) =
    LeftComodule(c.carrier, c, c.duplicator)

"""
    validate_left_comodule(M::LeftComodule; verbose=false) -> Bool

Check the left-comodule axioms element-wise:

1. **First-component law (counit, on positions):** for each `x ∈ X(1)`,
   `coaction.on_pos(x) = (i, mbar)` for some `i ∈ c(1)` and
   `mbar : c[i] → X.positions`, and `mbar(id_at_i) == x`.

2. **Counit law (on directions):** for every `x` and `a ∈ X[x]`,
   `coaction♯_x(id_at_i, a) == a`.

3. **Coassociativity:** for every triple `(b1, b2, a)` with `b1 ∈ c[i]`,
   `b2 ∈ c[jbar_i(b1)]`, `a ∈ X[mbar(b1 ; b2)]`, the two ways of
   collapsing match:

       coaction♯_x((b1 ; b2, a))  ==  coaction♯_x(b1, coaction♯_{mbar(b1)}(b2, a))

   ("first compose b1 and b2 in c, then step in λ" equals
   "first step b2-a in λ at the X-position visited by b1, then step b1").
"""
function validate_left_comodule(M::LeftComodule; verbose::Bool=false)
    X = M.carrier
    c = M.base.carrier
    λ = M.coaction
    pp = X.positions
    pp isa FinPolySet ||
        error("validate_left_comodule requires finite carrier positions")

    # Cache λ.on_pos outputs and identity directions on the base.
    i_at    = Dict()
    mbar_at = Dict()
    id_in_c = Dict()
    for x in pp.elements
        i, mbar = λ.on_positions.f(x)
        i_at[x] = i
        mbar_at[x] = mbar
    end
    for j in c.positions.elements
        id_in_c[j] = M.base.eraser.on_directions.f(j).f(:pt)
    end

    # Law 1: first-component / counit on positions
    for x in pp.elements
        i = i_at[x]
        id_i = id_in_c[i]
        if !haskey(mbar_at[x], id_i)
            verbose && println("Law 1 (positions) failed at $x: id_$i not in mbar keys")
            return false
        end
        if mbar_at[x][id_i] != x
            verbose && println("Law 1 (positions) failed at $x: mbar(id_$i) = $(mbar_at[x][id_i]) ≠ $x")
            return false
        end
    end

    # Law 2: counit on directions
    for x in pp.elements
        i = i_at[x]
        id_i = id_in_c[i]
        Dx = direction_at(X, x)::FinPolySet
        for a in Dx.elements
            got = λ.on_directions.f(x).f((id_i, a))
            if got != a
                verbose && println("Law 2 (counit, directions) failed at ($x, $a): λ♯ = $got ≠ $a")
                return false
            end
        end
    end

    # Law 3: coassoc
    for x in pp.elements
        i = i_at[x]
        Di = direction_at(c, i)::FinPolySet
        for b1 in Di.elements
            j = M.base.duplicator.on_positions.f(i)[2][b1]
            Dj = direction_at(c, j)::FinPolySet
            x_after_b1 = mbar_at[x][b1]
            # By coassoc on positions, λ.on_pos(x_after_b1) should have first
            # component j; if not, that's already a coassoc-on-positions failure.
            i_after = i_at[x_after_b1]
            if i_after != j
                verbose && println("Coassoc (positions) failed at ($x, $b1): i_after=$i_after, expected $j")
                return false
            end
            for b2 in Dj.elements
                bb = M.base.duplicator.on_directions.f(i).f((b1, b2))
                # mbar_at[x][bb] should equal mbar_at[x_after_b1][b2]
                pos_after = mbar_at[x][bb]
                if mbar_at[x_after_b1][b2] != pos_after
                    verbose && println("Coassoc (positions, second-step) failed at ($x, $b1, $b2)")
                    return false
                end
                Da = direction_at(X, pos_after)::FinPolySet
                for a in Da.elements
                    lhs = λ.on_directions.f(x).f((bb, a))
                    inner = λ.on_directions.f(x_after_b1).f((b2, a))
                    rhs = λ.on_directions.f(x).f((b1, inner))
                    if lhs != rhs
                        verbose && println("Coassoc (directions) failed at ($x, $b1, $b2, $a): $lhs ≠ $rhs")
                        return false
                    end
                end
            end
        end
    end

    true
end

# Bicomodules
# ============================================================
#
# A bicomodule `(c, X, d)` is a polynomial `X` equipped with a left
# `c`-coaction `λ_L : X → c ▷ X` and a right `d`-coaction `λ_R : X → X ▷ d`,
# satisfying the comodule laws on each side plus a compatibility axiom
# (the two coactions commute, modulo the associator of `▷`).
#
# Niu/Spivak Chapter 8: bicomodules over `(c, d)` correspond to
# *prafunctors* between the categories `cat(c)` and `cat(d)`. Functors
# `F : cat(c) → cat(d)` factor through the prafunctor / bicomodule story
# in the obvious way.

"""
    Bicomodule(carrier, left_base, right_base, left_coaction, right_coaction)

A bicomodule over `(left_base, right_base)`. The constructor type-checks
the coaction shapes:

- `left_coaction : carrier → left_base.carrier ▷ carrier`
- `right_coaction : carrier → carrier ▷ right_base.carrier`

RightComodule and compatibility axioms are not checked at construction —
use [`validate_bicomodule`](@ref).
"""
struct Bicomodule
    carrier::Polynomial
    left_base::Comonoid
    right_base::Comonoid
    left_coaction::Lens
    right_coaction::Lens
    function Bicomodule(carrier::Polynomial, left_base::Comonoid, right_base::Comonoid,
                        left_coaction::Lens, right_coaction::Lens)
        left_coaction.dom == carrier ||
            error("Bicomodule: left_coaction.dom ≠ carrier")
        left_coaction.cod == subst(left_base.carrier, carrier) ||
            error("Bicomodule: left_coaction.cod ≠ left_base.carrier ▷ carrier")
        right_coaction.dom == carrier ||
            error("Bicomodule: right_coaction.dom ≠ carrier")
        right_coaction.cod == subst(carrier, right_base.carrier) ||
            error("Bicomodule: right_coaction.cod ≠ carrier ▷ right_base.carrier")
        new(carrier, left_base, right_base, left_coaction, right_coaction)
    end
end

function show(io::IO, B::Bicomodule)
    print(io, "Bicomodule(")
    show(io, B.left_base.carrier)
    print(io, " ▷ ")
    show(io, B.carrier)
    print(io, " ▷ ")
    show(io, B.right_base.carrier)
    print(io, ")")
end

"""
    regular_bicomodule(c::Comonoid) -> Bicomodule

The regular bicomodule on `c`: carrier = `c.carrier`, both bases are
`c`, both coactions are `c.duplicator`. Validates iff `c` satisfies the
comonoid laws.
"""
function regular_bicomodule(c::Comonoid)
    Bicomodule(c.carrier, c, c, c.duplicator, c.duplicator)
end

"""
    validate_bicomodule(B::Bicomodule; verbose=false) -> Bool

Check the bicomodule axioms element-wise. The result is `true` iff:

- The right c-comodule laws hold for `(carrier, right_base, right_coaction)`
  (delegated to [`validate_right_comodule`](@ref) — full counit + coassoc).
- The left c-comodule laws hold for `(carrier, left_base, left_coaction)`
  (delegated to [`validate_left_comodule`](@ref) — full counit + coassoc).
- **Compatibility (positions):** for every `x ∈ X(1)` and every composable
  `(b, a)` with `b ∈ left_base[i]` and `a ∈ X[mbar_L(b)]`,
  `mbar_R_at_mbar_L_b(a) == mbar_R_at_x(λ_L♯_x(b, a))`. ("Stepping in `c`
  by `b` then in `X` by `a`" lands on the same `d`-position as "stepping in
  `X` directly by the composite that `λ_L` lifts `(b, a)` to.")
- **Compatibility (directions):** for every `x` and every triple
  `(b ∈ c[i], a ∈ X[mbar_L(b)], e ∈ d[mbar_R_at_mbar_L_b(a)])`,
  `λ_L♯_x(b, λ_R♯_{mbar_L(b)}(a, e)) == λ_R♯_x(λ_L♯_x(b, a), e)`. (The
  left-then-right and right-then-left ways of folding a c-X-d triple into
  an X-direction agree.)

Together these cover the full bicomodule compatibility square element-wise,
without needing to construct the associator of `▷` as a lens.
"""
function validate_bicomodule(B::Bicomodule; verbose::Bool=false)
    X = B.carrier
    pp = X.positions
    pp isa FinPolySet ||
        error("validate_bicomodule requires finite carrier positions")

    cL = B.left_base.carrier
    cR = B.right_base.carrier
    λL = B.left_coaction
    λR = B.right_coaction

    # --- Right-side checks: delegate to validate_right_comodule ---
    M_right = RightComodule(X, B.right_base, λR)
    if !validate_right_comodule(M_right; verbose=verbose)
        verbose && println("Right-side comodule laws failed.")
        return false
    end

    # --- Left-side checks: delegate to validate_left_comodule ---
    M_left = LeftComodule(X, B.left_base, λL)
    if !validate_left_comodule(M_left; verbose=verbose)
        verbose && println("Left-side comodule laws failed.")
        return false
    end

    # --- Compatibility law, element-wise on positions and directions ---
    # The bicomodule compatibility square (modulo the associator of `▷`)
    # asserts that "step left then right" agrees with "step right then left"
    # on the c-X-d component data. We unfold the law into element checks
    # over composable triples (b, a, e).
    for x in pp.elements
        i, mbar_L = λL.on_positions.f(x)
        _, mbar_R_x = λR.on_positions.f(x)
        DcL_i = direction_at(cL, i)::FinPolySet
        for b in DcL_i.elements
            x_b = mbar_L[b]
            _, mbar_R_xb = λR.on_positions.f(x_b)
            DX_xb = direction_at(X, x_b)::FinPolySet
            for a in DX_xb.elements
                # Position-level compatibility:
                #   mbar_R_xb(a)  ==  mbar_R_x(λ_L♯_x(b, a))
                # i.e. the d-position reached by "left b then right a from x_b"
                # matches the d-position reached by "right [composite from
                # left-lifting (b, a)] from x" directly.
                lifted_in_X = λL.on_directions.f(x).f((b, a))
                if mbar_R_xb[a] != mbar_R_x[lifted_in_X]
                    verbose && println("Compatibility (positions) failed at ($x, $b, $a): " *
                                       "mbar_R_xb($a) = $(mbar_R_xb[a]) ≠ $(mbar_R_x[lifted_in_X]) = mbar_R_x(λ_L♯)")
                    return false
                end

                # Direction-level compatibility:
                #   λ_L♯_x(b, λ_R♯_{x_b}(a, e))  ==  λ_R♯_x(λ_L♯_x(b, a), e)
                # for each e ∈ d[mbar_R_xb(a)].
                Dd = direction_at(cR, mbar_R_xb[a])::FinPolySet
                for e in Dd.elements
                    inner_R = λR.on_directions.f(x_b).f((a, e))
                    lhs = λL.on_directions.f(x).f((b, inner_R))
                    rhs = λR.on_directions.f(x).f((lifted_in_X, e))
                    if lhs != rhs
                        verbose && println("Compatibility (directions) failed at ($x, $b, $a, $e): $lhs ≠ $rhs")
                        return false
                    end
                end
            end
        end
    end

    true
end
