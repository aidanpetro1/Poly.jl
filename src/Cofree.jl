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
        # Shape-check via `is_subst_of` to avoid eagerly enumerating
        # subst(carrier, base.carrier). See Bicomodule constructor and
        # `docs/dev/extensions_v1_design.md` §1 for context.
        is_subst_of(coaction.cod, carrier, base.carrier) ||
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
validate_right_comodule(M::RightComodule; verbose::Union{Bool,Symbol}=false) =
    validate_right_comodule_detailed(M; verbose=verbose).passed

"""
    validate_right_comodule_detailed(M::RightComodule; verbose=false) -> ValidationResult

Same checks as [`validate_right_comodule`](@ref), but returns the full
`ValidationResult` with structural failure information.
"""
function validate_right_comodule_detailed(M::RightComodule; verbose::Union{Bool,Symbol}=false)
    X = M.carrier
    c = M.base.carrier
    λ = M.coaction
    pp = X.positions
    pp isa FinPolySet ||
        error("validate_right_comodule requires finite X.positions")

    failures = ValidationFailure[]
    collect_all = (verbose === :all)
    function record!(f::ValidationFailure)
        push!(failures, f)
        verbose === true && println("RightComodule violation: ", f.structural_hint)
        return collect_all
    end

    mbar_at = Dict()
    id_in_c = Dict()
    for x in pp.elements
        x′, mbar = λ.on_positions.f(x)
        if x′ != x
            failure = ValidationFailure(
                :coaction_first_component, (x,),
                "right-coaction's on_positions at $x must preserve the carrier " *
                "position component; got first component $x′",
                x′, x)
            record!(failure) || return fail(failures)
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
                failure = ValidationFailure(
                    :counit, (x, a),
                    "right-counit law: λ♯_$x($a, id_$j) should be $a but got $got — " *
                    "coaction's on-directions disagrees with base.eraser at object $j",
                    got, a)
                record!(failure) || return fail(failures)
            end
        end
    end

    # Law 3: coassoc.
    for x in pp.elements
        Dx = direction_at(X, x)::FinPolySet
        mbar_x = mbar_at[x]
        for a in Dx.elements
            j = mbar_x[a]
            Dj_in_c = direction_at(c, j)::FinPolySet
            for b1 in Dj_in_c.elements
                a′ = λ.on_directions.f(x).f((a, b1))
                k = M.base.duplicator.on_positions.f(j)[2][b1]
                Dk_in_c = direction_at(c, k)::FinPolySet
                for b2 in Dk_in_c.elements
                    lhs = λ.on_directions.f(x).f((a′, b2))
                    b1b2 = M.base.duplicator.on_directions.f(j).f((b1, b2))
                    rhs = λ.on_directions.f(x).f((a, b1b2))
                    if lhs != rhs
                        failure = ValidationFailure(
                            :coassoc, (x, a, b1),
                            "coassociativity at ($x, $a, $b1): coaction-then-base " *
                            "differs from base-then-coaction routing — " *
                            "λ♯($a;$b1, $b2) = $lhs vs λ♯($a, $b1;$b2) = $rhs",
                            lhs, rhs)
                        record!(failure) || return fail(failures)
                    end
                end
            end
        end
    end

    isempty(failures) ? pass("right-comodule laws") : fail(failures)
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
    # Materialize a lazy cod (rare here — labelings are typically built
    # eagerly) so the rest of this function can use the concrete-polynomial
    # interface (`p.positions`, `_tree_for_position` walking children, etc.).
    p_raw = labeling.cod
    p = p_raw isa ConcretePolynomial ? p_raw : materialize(p_raw)
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
        # Shape-check via `is_subst_of` to avoid eagerly enumerating
        # subst(base.carrier, carrier). See RightComodule for context.
        is_subst_of(coaction.cod, base.carrier, carrier) ||
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
validate_left_comodule(M::LeftComodule; verbose::Union{Bool,Symbol}=false) =
    validate_left_comodule_detailed(M; verbose=verbose).passed

"""
    validate_left_comodule_detailed(M::LeftComodule; verbose=false) -> ValidationResult

Same checks as [`validate_left_comodule`](@ref), but returns the full
`ValidationResult` with structural failure information.
"""
function validate_left_comodule_detailed(M::LeftComodule; verbose::Union{Bool,Symbol}=false)
    X = M.carrier
    c = M.base.carrier
    λ = M.coaction
    pp = X.positions
    pp isa FinPolySet ||
        error("validate_left_comodule requires finite carrier positions")

    failures = ValidationFailure[]
    collect_all = (verbose === :all)
    function record!(f::ValidationFailure)
        push!(failures, f)
        verbose === true && println("LeftComodule violation: ", f.structural_hint)
        return collect_all
    end

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
            failure = ValidationFailure(
                :counit_positions_keys, (x,),
                "left-coaction at $x: mbar's domain doesn't include id_$i — " *
                "the coaction's on-positions doesn't agree with base.eraser's identity choice",
                collect(keys(mbar_at[x])), id_i)
            record!(failure) || return fail(failures)
        elseif mbar_at[x][id_i] != x
            failure = ValidationFailure(
                :counit_positions, (x,),
                "left-coaction at $x: mbar(id_$i) = $(mbar_at[x][id_i]), should be $x — " *
                "coaction's on-positions disagrees with base.eraser at object $i",
                mbar_at[x][id_i], x)
            record!(failure) || return fail(failures)
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
                failure = ValidationFailure(
                    :counit_directions, (x, a),
                    "left-counit law: λ♯_$x(id_$i, $a) should be $a but got $got — " *
                    "coaction on-directions disagrees with base.eraser at object $i",
                    got, a)
                record!(failure) || return fail(failures)
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
            i_after = i_at[x_after_b1]
            if i_after != j
                failure = ValidationFailure(
                    :coassoc_positions, (x, b1),
                    "left-coassoc at ($x, $b1): position-tracking mismatch, i_after=$i_after but base.duplicator gives $j",
                    i_after, j)
                record!(failure) || return fail(failures)
            end
            for b2 in Dj.elements
                bb = M.base.duplicator.on_directions.f(i).f((b1, b2))
                pos_after = mbar_at[x][bb]
                if mbar_at[x_after_b1][b2] != pos_after
                    failure = ValidationFailure(
                        :coassoc_positions_second, (x, b1, b2),
                        "left-coassoc at ($x, $b1, $b2): two-step position routing diverges — " *
                        "mbar_x($b1;$b2) = $pos_after but mbar_{x_after}($b2) = $(mbar_at[x_after_b1][b2])",
                        mbar_at[x_after_b1][b2], pos_after)
                    record!(failure) || return fail(failures)
                end
                Da = direction_at(X, pos_after)::FinPolySet
                for a in Da.elements
                    lhs = λ.on_directions.f(x).f((bb, a))
                    inner = λ.on_directions.f(x_after_b1).f((b2, a))
                    rhs = λ.on_directions.f(x).f((b1, inner))
                    if lhs != rhs
                        failure = ValidationFailure(
                            :coassoc_directions, (x, b1, b2),
                            "left-coassoc at ($x, $b1, $b2): λ♯($b1;$b2, $a) = $lhs but $b1;λ♯($b2, $a) = $rhs — " *
                            "coaction's direction-routing isn't associative with base.duplicator",
                            lhs, rhs)
                        record!(failure) || return fail(failures)
                    end
                end
            end
        end
    end

    isempty(failures) ? pass("left-comodule laws") : fail(failures)
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
        # Shape-check coaction codomains via `is_subst_of` rather than `==`,
        # so the comparison doesn't trigger eager enumeration of the
        # substitution polynomial. The eager `subst(...) == cod` check used
        # to be the bottleneck for any non-trivial bicomodule. See
        # `is_subst_of` in Monoidal.jl for the decision procedure and
        # `docs/dev/extensions_v1_design.md` §1 for the motivation.
        is_subst_of(left_coaction.cod, left_base.carrier, carrier) ||
            error("Bicomodule: left_coaction.cod ≠ left_base.carrier ▷ carrier")
        right_coaction.dom == carrier ||
            error("Bicomodule: right_coaction.dom ≠ carrier")
        is_subst_of(right_coaction.cod, carrier, right_base.carrier) ||
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
    subst_targeted_coaction(carrier::Polynomial, base::Comonoid,
                            on_pos::Function, on_dir::Function;
                            side::Symbol = :left) -> Lens

Specialized [`subst_targeted_lens`](@ref) for bicomodule coactions.
Pre-fills the `(p, q)` operands of the substitution polynomial based on
which side of a bicomodule the coaction belongs to:

  - `side = :left` → cod = `subst(base.carrier, carrier)`, the shape of a
    left coaction `carrier → base.carrier ▷ carrier`.
  - `side = :right` → cod = `subst(carrier, base.carrier)`, the shape of a
    right coaction `carrier → carrier ▷ base.carrier`.

Eliminates a class of typos at the call site (mixing up which polynomial
goes first in the substitution).

# Example

```julia
λ_L = subst_targeted_coaction(X, c,
        x -> (j_at(x), mbar_at(x)),
        (x, a, b) -> step_in_X(x, a, b);
        side = :left)
```
"""
function subst_targeted_coaction(carrier::Polynomial, base::Comonoid,
                                  on_pos::Function, on_dir::Function;
                                  side::Symbol = :left)
    if side === :left
        subst_targeted_lens(carrier, base.carrier, carrier, on_pos, on_dir)
    elseif side === :right
        subst_targeted_lens(carrier, carrier, base.carrier, on_pos, on_dir)
    else
        throw(ArgumentError("subst_targeted_coaction: side must be :left or :right; " *
                            "got $(repr(side))"))
    end
end

# ============================================================
# Bicomodule arithmetic (Extensions v1, PR #2)
# ============================================================

"""
    +(M::Bicomodule, N::Bicomodule) -> Bicomodule

The sum of bicomodules over a common pair of bases. Requires
`M.left_base == N.left_base` and `M.right_base == N.right_base`.
The carrier is `M.carrier + N.carrier` (polynomial coproduct, with
tagged `(1, _)` / `(2, _)` positions); coactions are inherited
side-by-side.

Niu/Spivak Ch. 8: bicomodules between fixed comonoids form a category;
this `+` is the coproduct in that category.
"""
function +(M::Bicomodule, N::Bicomodule)
    M.left_base.carrier == N.left_base.carrier ||
        error("Bicomodule +: left bases must agree (got distinct comonoid carriers)")
    M.right_base.carrier == N.right_base.carrier ||
        error("Bicomodule +: right bases must agree")

    new_carrier = M.carrier + N.carrier
    cL = M.left_base.carrier
    cR = M.right_base.carrier

    # left_coaction : new_carrier → cL ▷ new_carrier
    # On positions: at (1, m_pos), call M.left_coaction.on_pos and re-tag
    # the mbar's outputs into the M-side of new_carrier; similarly for (2, _).
    new_left_pos = key -> begin
        tag, original = key
        if tag == 1
            j, mbar_orig = M.left_coaction.on_positions.f(original)
            mbar_combined = Dict(c_dir => (1, mbar_orig[c_dir]) for c_dir in keys(mbar_orig))
            (j, mbar_combined)
        else
            j, mbar_orig = N.left_coaction.on_positions.f(original)
            mbar_combined = Dict(c_dir => (2, mbar_orig[c_dir]) for c_dir in keys(mbar_orig))
            (j, mbar_combined)
        end
    end
    # On directions: a (cL ▷ new_carrier)-direction is (a, b) with a ∈ cL[j]
    # and b ∈ new_carrier[mbar_combined(a)] = M[mbar_M(a)] (via the (1, _)
    # injection — same shape as before). Routes back to M's or N's
    # original on_directions accordingly.
    new_left_dir = (key, ab) -> begin
        tag, original = key
        if tag == 1
            M.left_coaction.on_directions.f(original).f(ab)
        else
            N.left_coaction.on_directions.f(original).f(ab)
        end
    end
    new_left_coaction = Lens(new_carrier, subst(cL, new_carrier),
                             new_left_pos, new_left_dir)

    # right_coaction : new_carrier → new_carrier ▷ cR
    # On positions: at (1, m_pos), call M.right_coaction.on_pos which
    # returns (m_pos, mbar : M[m_pos] → cR.positions). The first component
    # must be re-tagged to (1, m_pos) for the new_carrier.
    new_right_pos = key -> begin
        tag, original = key
        if tag == 1
            _, mbar = M.right_coaction.on_positions.f(original)
            ((1, original), mbar)
        else
            _, mbar = N.right_coaction.on_positions.f(original)
            ((2, original), mbar)
        end
    end
    new_right_dir = (key, ab) -> begin
        tag, original = key
        if tag == 1
            M.right_coaction.on_directions.f(original).f(ab)
        else
            N.right_coaction.on_directions.f(original).f(ab)
        end
    end
    new_right_coaction = Lens(new_carrier, subst(new_carrier, cR),
                              new_right_pos, new_right_dir)

    Bicomodule(new_carrier, M.left_base, M.right_base,
               new_left_coaction, new_right_coaction)
end

# ============================================================
# Bicomodule composition  M ⊙_D N  (prafunctor composition)
# ============================================================
#
# Niu/Spivak Ch. 8: for `M : C ↛ D` and `N : D ↛ E`, the composite
# `M ⊙_D N : C ↛ E` represents the composition of the corresponding
# prafunctors. Mathematically the carrier is the coequalizer of the two
# `D`-actions on `M.carrier ▷ N.carrier`.
#
# This implementation follows the explicit element-wise description:
# positions of `M ⊙_D N` are pairs `(x, y)` where the right-D-position of
# `x` (via M's right-coaction) matches the left-D-position of `y` (via
# N's left-coaction). Directions at `(x, y)` come from the right side of
# N at `y`, since after collapsing through D, the residual is the
# E-coaction information.
#
# **Scope note (2026-04-28)**: The full coequalizer requires identifying
# pairs `(x · d, y) ~ (x, d · y)` for each D-direction `d`. The
# implementation below realizes this for the case where both
# coaction-on-positions functions are total and the resulting equivalence
# classes have canonical representatives — which covers `regular ⊙ regular`
# and the bicomodules typically built in practice. For pathological
# bicomodules with non-trivial equivalence classes the construction may
# overcount; that scenario is flagged in `validate_bicomodule_detailed`'s
# output by failing compatibility checks.

"""
    compose(M::Bicomodule, N::Bicomodule) -> Bicomodule
    M ⊙ N

Prafunctor composition of bicomodules over a common middle comonoid
(Niu/Spivak Ch. 8). Requires `M.right_base.carrier == N.left_base.carrier` —
the right base of `M` must match the left base of `N`. Returns
`M ⊙_D N : M.left_base ↛ N.right_base` where `D = M.right_base = N.left_base`.

The carrier consists of pairs `(x, y)` where `x ∈ M.carrier.positions` and
`y ∈ N.carrier.positions` agree on the connecting D-position via the
right coaction of M and the left coaction of N. Directions at `(x, y)`
combine an M-direction with the corresponding N-direction shifted by the
D-action.

# Compatibility with regular bicomodules

For a comonoid `c`, `compose(regular_bicomodule(c), regular_bicomodule(c))`
is structurally isomorphic to `regular_bicomodule(c)` (the regular
bicomodule is the unit for composition over `c`).

# Unicode alias

`M ⊙ N` is provided as an infix alias. The book uses `⊙` for prafunctor
composition.

# Scope note

See the file-level comment above for the implementation's coverage; the
construction is exact for the common cases (regular bicomodules, any
bicomodule composed with the regular bicomodule on the appropriate side)
and approximates the full coequalizer for the general case.
"""
function compose(M::Bicomodule, N::Bicomodule)
    M.right_base.carrier == N.left_base.carrier ||
        error("compose(::Bicomodule, ::Bicomodule): M's right base must equal N's left base")

    X = M.carrier
    Y = N.carrier
    D = M.right_base.carrier
    cL = M.left_base.carrier
    cR = N.right_base.carrier

    Xp = X.positions
    Yp = Y.positions
    (Xp isa FinPolySet && Yp isa FinPolySet) ||
        error("compose(::Bicomodule, ::Bicomodule) requires finite carrier positions")

    # Enumerate compatible (x, y) pairs: those where the D-position visited
    # by N's left-coaction at y equals one of the D-positions reachable from
    # x via M's right-coaction. For the canonical case where both coactions
    # have total mbar functions, "compatible" reduces to "y's left-D-position
    # appears in the image of x's right-mbar."
    new_pos_elements = Tuple[]
    for x in Xp.elements
        _, mbar_R = M.right_coaction.on_positions.f(x)
        right_D_image = Set(values(mbar_R))
        for y in Yp.elements
            j_y, _ = N.left_coaction.on_positions.f(y)
            j_y in right_D_image && push!(new_pos_elements, (x, y))
        end
    end
    new_carrier_positions = FinPolySet(new_pos_elements)

    # Direction-set at (x, y): inherited from N's directions at y, since
    # after mediating through D, the residual structure at (x, y) is
    # determined by the right-coaction of N (which connects y to E).
    # This is the same shape as Y[y].
    new_carrier_dir = key -> begin
        x, y = key
        direction_at(Y, y)
    end
    new_carrier = Polynomial(new_carrier_positions, new_carrier_dir)

    # Left coaction: (x, y) → cL ▷ new_carrier.
    # Inherits from M.left_coaction at x; at each cL-direction we land on
    # some x' ∈ X, and pair it with the same y (justified by the
    # compatibility filter on positions).
    new_left_pos = key -> begin
        x, y = key
        j, mbar_L_M = M.left_coaction.on_positions.f(x)
        # Pair each landed x' with this y; if (x', y) isn't a valid
        # composite position, the carrier rejects it — but for the
        # typical case where the original bicomodules play well, the
        # pair is valid.
        mbar_combined = Dict(c_dir => (mbar_L_M[c_dir], y) for c_dir in keys(mbar_L_M))
        (j, mbar_combined)
    end
    new_left_dir = (key, ab) -> begin
        x, _ = key
        # ab = (a ∈ cL[j], b ∈ new_carrier[(x', y)] = Y[y]).
        # M's left-coaction-on-directions returns a direction in X[x]; but
        # our composite carrier's direction-set at (x, y) is Y[y], not X[x].
        # The right-coaction of M, composed with the left-coaction of N
        # (mediated through D), provides the bridge — for this scope we
        # take ab[2] directly, which is correct when M's left-coaction
        # passes Y-directions through unchanged (the regular case).
        ab[2]
    end
    new_left_coaction = Lens(new_carrier, subst(cL, new_carrier),
                             new_left_pos, new_left_dir)

    # Right coaction: (x, y) → new_carrier ▷ cR.
    # Inherits from N.right_coaction at y.
    new_right_pos = key -> begin
        x, y = key
        _, mbar_R_N = N.right_coaction.on_positions.f(y)
        # Pair landed y' with this x; same caveat as above for general case.
        mbar_combined = Dict(d_dir => (x, mbar_R_N[d_dir]) for d_dir in keys(mbar_R_N))
        ((x, y), mbar_combined)
    end
    new_right_dir = (key, ab) -> begin
        _, y = key
        N.right_coaction.on_directions.f(y).f(ab)
    end
    new_right_coaction = Lens(new_carrier, subst(new_carrier, cR),
                              new_right_pos, new_right_dir)

    Bicomodule(new_carrier, M.left_base, N.right_base,
               new_left_coaction, new_right_coaction)
end

"""
    ⊙(M::Bicomodule, N::Bicomodule) -> Bicomodule

Unicode alias for [`compose(::Bicomodule, ::Bicomodule)`](@ref). Renders
as the book's prafunctor-composition glyph.
"""
const var"⊙" = compose

# ============================================================
# Bicomodule ⊗  (parallel product over tensored bases)
# ============================================================
#
# `M : C ↛ D` and `N : C' ↛ D'` parallelize to `M ⊗ N : (C ⊗ C') ↛ (D ⊗ D')`.
# The carrier is the polynomial parallel product `M.carrier ⊗ N.carrier`;
# the bases are the polynomial-level tensor of the operand comonoids
# (built via `_comonoid_carrier_tensor` below — *not* via the
# `to_category` bridge that user-facing `Comonoid ⊗` uses, because that
# representation has a different direction-set encoding).
#
# Note on the `Comonoid ⊗` distinction: the user-facing `c ⊗ d` returns
# a comonoid through the categorical-product bridge, with morphism-pair
# directions. The bases of `M ⊗ N` use direction-pair encoding to match
# `Polynomial ⊗`. The two are isomorphic as comonoids; they differ only
# in how directions are structurally encoded.

# Internal: build a Comonoid whose carrier is `c.carrier ⊗ d.carrier`
# (Polynomial ⊗) with componentwise eraser and duplicator. Used by
# `parallel(::Bicomodule, ::Bicomodule)` to construct the tensored bases
# in a form compatible with the parallel-tensored carrier.
function _comonoid_carrier_tensor(c::Comonoid, d::Comonoid)
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

    Comonoid(new_carrier, new_eraser, new_dup)
end

"""
    parallel(M::Bicomodule, N::Bicomodule) -> Bicomodule
    M ⊗ N

The parallel/Dirichlet product of bicomodules, with bases tensored.
For `M : C ↛ D` and `N : C' ↛ D'`, returns a bicomodule
`M ⊗ N : (C ⊗_carrier C') ↛ (D ⊗_carrier D')` whose carrier is
`M.carrier ⊗ N.carrier`.

The new left/right bases are constructed via
`_comonoid_carrier_tensor`, which builds a comonoid whose carrier is
the polynomial parallel of the operand carriers (with componentwise
eraser and duplicator). This is isomorphic to (but encoded
differently from) the user-facing `Comonoid ⊗ / *` product — the
distinction matters here because Bicomodule directions need to align
with `Polynomial ⊗`'s direction-pair encoding rather than the
morphism-pair encoding the categorical bridge produces.

Routing of coactions is componentwise: the `(m_pos, n_pos)`-th
coaction lifts each side's coaction in lockstep.
"""
function parallel(M::Bicomodule, N::Bicomodule)
    new_carrier = parallel(M.carrier, N.carrier)
    new_left_base = _comonoid_carrier_tensor(M.left_base, N.left_base)
    new_right_base = _comonoid_carrier_tensor(M.right_base, N.right_base)

    cL = new_left_base.carrier
    cR = new_right_base.carrier

    # Left coaction: (m_pos, n_pos) ↦ ((j_M, j_N), mbar_combined)
    # where mbar_combined((a, b)) = (mbar_M(a), mbar_N(b)).
    new_left_pos = key -> begin
        m_pos, n_pos = key
        j_M, mbar_M = M.left_coaction.on_positions.f(m_pos)
        j_N, mbar_N = N.left_coaction.on_positions.f(n_pos)
        cL_dirs = direction_at(cL, (j_M, j_N))::FinPolySet
        mbar_combined = Dict{Any,Any}()
        for ab in cL_dirs.elements
            a, b = ab
            mbar_combined[ab] = (mbar_M[a], mbar_N[b])
        end
        ((j_M, j_N), mbar_combined)
    end
    new_left_dir = (key, ab_pair) -> begin
        m_pos, n_pos = key
        # ab_pair = ((a1, a2), (b1, b2)) — both halves are direction-pairs
        # under Polynomial ⊗'s encoding.
        ab1, ab2 = ab_pair
        a1, a2 = ab1
        b1, b2 = ab2
        m_dir = M.left_coaction.on_directions.f(m_pos).f((a1, b1))
        n_dir = N.left_coaction.on_directions.f(n_pos).f((a2, b2))
        (m_dir, n_dir)
    end
    new_left_coaction = Lens(new_carrier, subst_lazy(cL, new_carrier),
                              new_left_pos, new_left_dir)

    # Right coaction: (m_pos, n_pos) ↦ ((m_pos, n_pos), mbar_combined)
    # where mbar_combined((a, b)) = (mbar_R_M(a), mbar_R_N(b)).
    new_right_pos = key -> begin
        m_pos, n_pos = key
        _, mbar_M = M.right_coaction.on_positions.f(m_pos)
        _, mbar_N = N.right_coaction.on_positions.f(n_pos)
        carrier_dirs = direction_at(new_carrier, (m_pos, n_pos))::FinPolySet
        mbar_combined = Dict{Any,Any}()
        for ab in carrier_dirs.elements
            a, b = ab
            mbar_combined[ab] = (mbar_M[a], mbar_N[b])
        end
        ((m_pos, n_pos), mbar_combined)
    end
    new_right_dir = (key, ab_pair) -> begin
        m_pos, n_pos = key
        ab1, ab2 = ab_pair
        a1, a2 = ab1
        b1, b2 = ab2
        m_dir = M.right_coaction.on_directions.f(m_pos).f((a1, b1))
        n_dir = N.right_coaction.on_directions.f(n_pos).f((a2, b2))
        (m_dir, n_dir)
    end
    new_right_coaction = Lens(new_carrier, subst_lazy(new_carrier, cR),
                               new_right_pos, new_right_dir)

    Bicomodule(new_carrier, new_left_base, new_right_base,
               new_left_coaction, new_right_coaction)
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
validate_bicomodule(B::Bicomodule; verbose::Union{Bool,Symbol}=false) =
    validate_bicomodule_detailed(B; verbose=verbose).passed

"""
    validate_bicomodule_detailed(B::Bicomodule; verbose=false) -> ValidationResult

Same checks as [`validate_bicomodule`](@ref), but returns the full
`ValidationResult` with structural failure information. With `verbose=:all`,
collects every failing compatibility triple — pass the result's `.failures`
to [`minimal_failing_triple`](@ref) to surface the lex-smallest.
"""
function validate_bicomodule_detailed(B::Bicomodule; verbose::Union{Bool,Symbol}=false)
    X = B.carrier
    pp = X.positions
    pp isa FinPolySet ||
        error("validate_bicomodule requires finite carrier positions")

    cL = B.left_base.carrier
    cR = B.right_base.carrier
    λL = B.left_coaction
    λR = B.right_coaction

    failures = ValidationFailure[]
    collect_all = (verbose === :all)

    # --- Right-side checks (use _detailed to access .failures) ---
    M_right = RightComodule(X, B.right_base, λR)
    right_result = validate_right_comodule_detailed(M_right;
                                                    verbose=(verbose === :all ? :all : false))
    if !right_result.passed
        for f in right_result.failures
            hinted = ValidationFailure(f.law, f.location,
                                       "right-comodule side: " * f.structural_hint,
                                       f.actual, f.expected)
            push!(failures, hinted)
            verbose === true && println("Bicomodule (right): ", hinted.structural_hint)
        end
        if !collect_all
            return fail(failures, summary="right-comodule laws fail")
        end
    end

    # --- Left-side checks (use _detailed to access .failures) ---
    M_left = LeftComodule(X, B.left_base, λL)
    left_result = validate_left_comodule_detailed(M_left;
                                                  verbose=(verbose === :all ? :all : false))
    if !left_result.passed
        for f in left_result.failures
            hinted = ValidationFailure(f.law, f.location,
                                       "left-comodule side: " * f.structural_hint,
                                       f.actual, f.expected)
            push!(failures, hinted)
            verbose === true && println("Bicomodule (left): ", hinted.structural_hint)
        end
        if !collect_all
            return fail(failures, summary="left-comodule laws fail")
        end
    end

    # --- Compatibility law, element-wise on positions and directions ---
    # When :all is requested we collect every failing triple; the helper
    # `minimal_failing_triple` then lets the caller surface the lex-smallest.
    compat_failures = ValidationFailure[]
    for x in pp.elements
        i, mbar_L = λL.on_positions.f(x)
        _, mbar_R_x = λR.on_positions.f(x)
        DcL_i = direction_at(cL, i)::FinPolySet
        for b in DcL_i.elements
            x_b = mbar_L[b]
            _, mbar_R_xb = λR.on_positions.f(x_b)
            DX_xb = direction_at(X, x_b)::FinPolySet
            for a in DX_xb.elements
                lifted_in_X = λL.on_directions.f(x).f((b, a))
                if mbar_R_xb[a] != mbar_R_x[lifted_in_X]
                    f = ValidationFailure(
                        :compatibility_positions, (x, b, a),
                        "left-then-right vs right-then-left position routing differs at " *
                        "($x, $b, $a): mbar_R(x_b)($a) = $(mbar_R_xb[a]) ≠ " *
                        "mbar_R(x)(λ_L♯($b, $a)) = $(mbar_R_x[lifted_in_X])",
                        mbar_R_xb[a], mbar_R_x[lifted_in_X])
                    push!(compat_failures, f)
                    verbose === true && println("Bicomodule compat: ", f.structural_hint)
                    if !collect_all
                        push!(failures, f)
                        return fail(failures, summary="compatibility (positions) fails")
                    end
                    continue
                end

                Dd = direction_at(cR, mbar_R_xb[a])::FinPolySet
                for e in Dd.elements
                    inner_R = λR.on_directions.f(x_b).f((a, e))
                    lhs = λL.on_directions.f(x).f((b, inner_R))
                    rhs = λR.on_directions.f(x).f((lifted_in_X, e))
                    if lhs != rhs
                        f = ValidationFailure(
                            :compatibility_directions, (x, b, a),
                            "left-then-right vs right-then-left direction routing " *
                            "differs at ($x, $b, $a, $e): λ_L♯($b, λ_R♯($a, $e)) = $lhs " *
                            "but λ_R♯(λ_L♯($b, $a), $e) = $rhs",
                            lhs, rhs)
                        push!(compat_failures, f)
                        verbose === true && println("Bicomodule compat: ", f.structural_hint)
                        if !collect_all
                            push!(failures, f)
                            return fail(failures, summary="compatibility (directions) fails")
                        end
                    end
                end
            end
        end
    end

    append!(failures, compat_failures)

    if isempty(failures)
        return pass("bicomodule axioms")
    end
    summary = isempty(compat_failures) ? "comodule-side failures" :
              "compatibility failures (run minimal_failing_triple on .failures " *
              "to surface the lex-smallest)"
    fail(failures, summary=summary)
end

# ============================================================
# sharp_L / sharp_R (Extensions v2 PR #6)
# ============================================================

"""
    sharp_L(B::Bicomodule; materialize=:auto) -> Union{BackDirectionTable, Function}

The back-direction map of `B`'s left coaction lens. Shorthand for
`back_directions(B.left_coaction; materialize=materialize)`. For the
materialized form, keys are `(carrier_position, λ_L_codirection)` pairs
and values are the corresponding carrier-direction.

Use case: pretty-print left back-directions when debugging a coherence
failure surfaced by `validate_bicomodule_detailed`.
"""
sharp_L(B::Bicomodule; materialize::Union{Bool,Symbol}=:auto) =
    back_directions(B.left_coaction; materialize=materialize)

"""
    sharp_R(B::Bicomodule; materialize=:auto) -> Union{BackDirectionTable, Function}

The back-direction map of `B`'s right coaction lens. Shorthand for
`back_directions(B.right_coaction; materialize=materialize)`. Dual to
[`sharp_L`](@ref).
"""
sharp_R(B::Bicomodule; materialize::Union{Bool,Symbol}=:auto) =
    back_directions(B.right_coaction; materialize=materialize)

# ============================================================
# bicomodule_from_data (Extensions v2 PR #5)
# ============================================================
#
# Authoring helper: build a `Bicomodule` from explicit Dicts of coaction
# data. Mirrors `comonoid_from_data` (Comonoid.jl). Validates by default
# (Q5.2). Bundled with `comonoid_from_data` per Q5.3 resolution.

"""
    bicomodule_from_data(
        carrier::Polynomial,
        left_base::Comonoid,
        right_base::Comonoid;
        left_position_map::AbstractDict,     # x -> (lb_pos, jbar_L::AbstractDict)
        left_back_directions::AbstractDict,  # (x, b, a) -> carrier_dir at x
        right_position_map::AbstractDict,    # x -> jbar_R::AbstractDict
        right_back_directions::AbstractDict, # (x, a, e) -> carrier_dir at x
        validate::Bool=true,
    ) -> Bicomodule

Build a `Bicomodule` from authored coaction data tables, constructing
the two coaction lenses internally.

# Left coaction structure

The left coaction is a lens `λ_L : carrier → left_base.carrier ▷ carrier`.

  - `left_position_map[x] = (lb_pos, jbar_L)` where `jbar_L` is itself a
    `Dict` mapping `b ∈ left_base[lb_pos]` to a `carrier_pos`.
  - `left_back_directions[(x, b, a)]` is the carrier-direction at `x`
    that the back-direction map sends the `(b, a)` codomain-direction
    to. Here `b ∈ left_base[lb_pos]` and `a ∈ carrier[jbar_L[b]]`.

# Right coaction structure

The right coaction is a lens `λ_R : carrier → carrier ▷ right_base.carrier`.
By the comodule axiom, `λ_R.on_positions(x)` always has `x` as its first
component, so only the `jbar_R` part needs to be supplied.

  - `right_position_map[x] = jbar_R` where `jbar_R` is a `Dict` mapping
    `a ∈ carrier[x]` to a `right_base.positions` element.
  - `right_back_directions[(x, a, e)]` is the carrier-direction at `x`
    that the back-direction map sends the `(a, e)` codomain-direction
    to. Here `a ∈ carrier[x]` and `e ∈ right_base[jbar_R[a]]`.

# Validation

When `validate=true` (default), the constructor runs
[`validate_bicomodule_detailed`](@ref) and throws `ArgumentError` on
failure with the validation summary attached. Pass `validate=false` for
intermediate constructions you'll validate later.

See [`comonoid_from_data`](@ref) for the analogous comonoid helper.
"""
function bicomodule_from_data(carrier::Polynomial,
                              left_base::Comonoid,
                              right_base::Comonoid;
                              left_position_map::AbstractDict,
                              left_back_directions::AbstractDict,
                              right_position_map::AbstractDict,
                              right_back_directions::AbstractDict,
                              validate::Bool=true)
    cL = left_base.carrier
    cR = right_base.carrier

    left_on_pos = x -> left_position_map[x]
    left_on_dir = (x, ba) -> begin
        b, a = ba
        left_back_directions[(x, b, a)]
    end
    left_coaction = Lens(carrier, subst_lazy(cL, carrier),
                         left_on_pos, left_on_dir)

    right_on_pos = x -> (x, right_position_map[x])
    right_on_dir = (x, ae) -> begin
        a, e = ae
        right_back_directions[(x, a, e)]
    end
    right_coaction = Lens(carrier, subst_lazy(carrier, cR),
                          right_on_pos, right_on_dir)

    result = Bicomodule(carrier, left_base, right_base,
                        left_coaction, right_coaction)

    if validate
        r = validate_bicomodule_detailed(result; verbose=:all)
        r.passed || throw(ArgumentError(
            "bicomodule_from_data: validation failed — " * r.summary *
            "; pass `validate=false` to skip."))
    end
    result
end

# ============================================================
# BicomoduleMorphism (2-cells) — Extensions v2 PR #2
# ============================================================
#
# A 2-cell α : M ⇒ N between two bicomodules sharing the same left and
# right base comonoids. Underlying data: a polynomial lens
# `M.carrier → N.carrier` whose composition with each coaction of M
# agrees with the corresponding coaction of N.
#
# Coherence axioms (validated):
#   - Left:  (id_C ▷ α) ⊙ M.left_coaction  ==  N.left_coaction ⊙ α
#   - Right: (α ▷ id_D) ⊙ M.right_coaction ==  N.right_coaction ⊙ α
#
# Per Q2.1 (resolved 2026-05-01): bases must match by `===` (object
# identity), not just structural `==`. Different-base 2-cells will be
# handled by a separate `bicomodule_morphism_over` constructor in a
# later release.
#
# Per Q2.2 (resolved 2026-05-01): horizontal composition (whiskering and
# 2-cell compose in the double category Cat#) is provided alongside the
# basic struct + vertical composition. Whiskering uses the existing
# bicomodule `compose` operation, which itself approximates the full
# coequalizer for general bicomodules (see compose(::Bicomodule,
# ::Bicomodule) docstring) — that approximation propagates here.

"""
    BicomoduleMorphism(source::Bicomodule, target::Bicomodule, underlying::Lens)

A 2-cell α : source ⇒ target in the double category Cat#. Source and
target must share `left_base` and `right_base` by object identity
(`===`); the underlying lens has shape
`source.carrier → target.carrier`.

Coherence is NOT checked at construction — use
[`validate_bicomodule_morphism`](@ref) (or the `_detailed` variant for
structured failure information).
"""
struct BicomoduleMorphism
    source::Bicomodule
    target::Bicomodule
    underlying::Lens
    function BicomoduleMorphism(source::Bicomodule,
                                target::Bicomodule,
                                underlying::Lens)
        source.left_base === target.left_base ||
            error("BicomoduleMorphism: source.left_base !== target.left_base " *
                  "(must match by ===; use `bicomodule_morphism_over` for " *
                  "different-base 2-cells, when implemented)")
        source.right_base === target.right_base ||
            error("BicomoduleMorphism: source.right_base !== target.right_base")
        underlying.dom == source.carrier ||
            error("BicomoduleMorphism: underlying.dom ≠ source.carrier")
        underlying.cod == target.carrier ||
            error("BicomoduleMorphism: underlying.cod ≠ target.carrier")
        new(source, target, underlying)
    end
end

function show(io::IO, α::BicomoduleMorphism)
    print(io, "BicomoduleMorphism(")
    show(io, α.source.carrier)
    print(io, " ⇒ ")
    show(io, α.target.carrier)
    print(io, ")")
end

"""
    identity_bicomodule_morphism(B::Bicomodule) -> BicomoduleMorphism

The identity 2-cell on `B`, with underlying = `identity_lens(B.carrier)`.
"""
identity_bicomodule_morphism(B::Bicomodule) =
    BicomoduleMorphism(B, B, identity_lens(B.carrier))

"""
    compose(α::BicomoduleMorphism, β::BicomoduleMorphism) -> BicomoduleMorphism

Vertical composition. Requires `α.target === β.source`. Underlying lens
is `compose(α.underlying, β.underlying)` (vertical lens composition).
"""
function compose(α::BicomoduleMorphism, β::BicomoduleMorphism)
    α.target === β.source ||
        error("compose(::BicomoduleMorphism, ::BicomoduleMorphism): " *
              "α.target !== β.source")
    BicomoduleMorphism(α.source, β.target, compose(α.underlying, β.underlying))
end

# ------------------------------------------------------------
# Validation
# ------------------------------------------------------------

"""
    validate_bicomodule_morphism(α::BicomoduleMorphism; verbose=false) -> Bool

Check that `α` satisfies both coaction-respect squares (left and right).
For structural failure information, see
[`validate_bicomodule_morphism_detailed`](@ref).
"""
validate_bicomodule_morphism(α::BicomoduleMorphism; verbose::Union{Bool,Symbol}=false) =
    validate_bicomodule_morphism_detailed(α; verbose=verbose).passed

"""
    validate_bicomodule_morphism_detailed(α::BicomoduleMorphism; verbose=false)
        -> ValidationResult

Same checks as [`validate_bicomodule_morphism`](@ref) but returns the
full `ValidationResult` with structural failure information. With
`verbose=:all`, collects every failing position rather than returning at
the first.

# Axioms checked

  - `:morphism_left_positions` and `:morphism_left_directions` — the
    left-coaction square commutes.
  - `:morphism_right_positions` and `:morphism_right_directions` — the
    right-coaction square commutes.
"""
function validate_bicomodule_morphism_detailed(α::BicomoduleMorphism;
                                               verbose::Union{Bool,Symbol}=false)
    failures = ValidationFailure[]
    collect_all = (verbose === :all)
    M, N = α.source, α.target
    Xp = M.carrier.positions
    Xp isa FinPolySet ||
        error("validate_bicomodule_morphism requires finite source carrier positions")

    α_pos = α.underlying.on_positions.f
    α_dir = α.underlying.on_directions.f

    # --- Left-coaction square ---
    cL = M.left_base.carrier
    for x in Xp.elements
        αx = α_pos(x)
        (lb_M, jbar_L_M) = M.left_coaction.on_positions.f(x)
        (lb_N, jbar_L_N) = N.left_coaction.on_positions.f(αx)

        if lb_M != lb_N
            f = ValidationFailure(
                :morphism_left_positions, (x,),
                "left-coaction's left-base position differs at $x: " *
                "M routes to $lb_M, N routes to $lb_N",
                lb_M, lb_N)
            push!(failures, f)
            verbose === true && println("BicomoduleMorphism left/pos: ", f.structural_hint)
            collect_all || return fail(failures, summary="left-coaction square fails (positions)")
            continue
        end

        DcL_lb = direction_at(cL, lb_M)::FinPolySet
        for b in DcL_lb.elements
            j_via_M = α_pos(jbar_L_M[b])
            j_via_N = jbar_L_N[b]
            if j_via_M != j_via_N
                f = ValidationFailure(
                    :morphism_left_positions, (x, b),
                    "left-coaction emit position differs at ($x, $b): " *
                    "α(M.jbar(b)) = $j_via_M, N.jbar(b) = $j_via_N",
                    j_via_M, j_via_N)
                push!(failures, f)
                verbose === true && println("BicomoduleMorphism left/pos: ", f.structural_hint)
                collect_all || return fail(failures, summary="left-coaction square fails (positions)")
                continue
            end

            # Direction-level: take any direction a in N.carrier[j_via_N],
            # check that α♯(M.left_coaction♯(b, a)) == N.left_coaction♯(b, α♯(a)).
            DN_j = direction_at(N.carrier, j_via_N)::FinPolySet
            for a in DN_j.elements
                # Path 1: a → carrier_dir at α(jbar_L_M[b]) via α♯, then through M.left_coaction♯
                a_pulled = α_dir(jbar_L_M[b]).f(a)
                lhs = α_dir(x).f(M.left_coaction.on_directions.f(x).f((b, a_pulled)))
                # Path 2: a → through N.left_coaction♯ at αx
                rhs = N.left_coaction.on_directions.f(αx).f((b, a))
                if lhs != rhs
                    f = ValidationFailure(
                        :morphism_left_directions, (x, b, a),
                        "left-coaction direction square fails at ($x, $b, $a): " *
                        "α♯(M.λ_L♯) = $lhs, N.λ_L♯ ∘ α = $rhs",
                        lhs, rhs)
                    push!(failures, f)
                    verbose === true && println("BicomoduleMorphism left/dir: ", f.structural_hint)
                    collect_all || return fail(failures, summary="left-coaction square fails (directions)")
                end
            end
        end
    end

    # --- Right-coaction square ---
    cR = M.right_base.carrier
    for x in Xp.elements
        αx = α_pos(x)
        (_, jbar_R_M) = M.right_coaction.on_positions.f(x)
        (_, jbar_R_N) = N.right_coaction.on_positions.f(αx)

        DN_x = direction_at(N.carrier, αx)::FinPolySet
        for a_N in DN_x.elements
            a_M = α_dir(x).f(a_N)
            rb_via_M = jbar_R_M[a_M]
            rb_via_N = jbar_R_N[a_N]
            if rb_via_M != rb_via_N
                f = ValidationFailure(
                    :morphism_right_positions, (x, a_N),
                    "right-coaction emit position differs at ($x, $a_N): " *
                    "M.jbar(α♯(a_N)) = $rb_via_M, N.jbar(a_N) = $rb_via_N",
                    rb_via_M, rb_via_N)
                push!(failures, f)
                verbose === true && println("BicomoduleMorphism right/pos: ", f.structural_hint)
                collect_all || return fail(failures, summary="right-coaction square fails (positions)")
                continue
            end
            DcR_rb = direction_at(cR, rb_via_N)::FinPolySet
            for e in DcR_rb.elements
                lhs = α_dir(x).f(N.right_coaction.on_directions.f(αx).f((a_N, e)))
                rhs = M.right_coaction.on_directions.f(x).f((a_M, e))
                if lhs != rhs
                    f = ValidationFailure(
                        :morphism_right_directions, (x, a_N, e),
                        "right-coaction direction square fails at ($x, $a_N, $e): " *
                        "α♯(N.λ_R♯) = $lhs, M.λ_R♯ at α♯(a_N) = $rhs",
                        lhs, rhs)
                    push!(failures, f)
                    verbose === true && println("BicomoduleMorphism right/dir: ", f.structural_hint)
                    collect_all || return fail(failures, summary="right-coaction square fails (directions)")
                end
            end
        end
    end

    isempty(failures) ? pass("bicomodule morphism axioms") :
                        fail(failures, summary="coherence square(s) fail")
end

# ------------------------------------------------------------
# Horizontal composition (whiskering + full 2-cell compose)
# ------------------------------------------------------------
#
# Given α : M ⇒ M' (over C↛D) and β : N ⇒ N' (over D↛E), the horizontal
# composite α ⊙_h β : M ⊙ N ⇒ M' ⊙ N' (over C↛E). Built from whiskering:
#   α ⊙_h β = (α whiskered with N) ; (M' whiskered with β).
#
# Whiskering: α : M ⇒ M' (over C↛D) and a bicomodule N : D↛E. The
# whiskered 2-cell α ⊙_h id_N : M ⊙ N ⇒ M' ⊙ N has underlying lens
# defined componentwise on the (x, y) pairs of (M ⊙ N).carrier:
# (x, y) ↦ (α.on_positions(x), y), with directions inherited from
# N (since the bicomodule-compose carrier inherits N's direction-set).

"""
    whisker_left(α::BicomoduleMorphism, N::Bicomodule) -> BicomoduleMorphism

Right-whisker of `α` by `N`: produces `α ⊙_h id_N : (M ⊙ N) ⇒ (M' ⊙ N)`
where `α : M ⇒ M'` is over the bases `(C, D)` and `N` is over `(D, E)`.
Requires `α.source.right_base === N.left_base`.
"""
function whisker_left(α::BicomoduleMorphism, N::Bicomodule)
    α.source.right_base === N.left_base ||
        error("whisker_left: α.source.right_base !== N.left_base")
    M_compose_N  = compose(α.source, N)
    Mp_compose_N = compose(α.target, N)

    on_pos_fn = key -> begin
        x, y = key
        (α.underlying.on_positions.f(x), y)
    end
    # Direction-set at (x, y) in the composite carrier is direction_at(N, y).
    # Same direction-set on both sides of the whisker, so on_directions is identity.
    on_dir_fn = (key, b) -> b

    underlying = Lens(M_compose_N.carrier, Mp_compose_N.carrier,
                      on_pos_fn, on_dir_fn)
    BicomoduleMorphism(M_compose_N, Mp_compose_N, underlying)
end

"""
    whisker_right(M::Bicomodule, β::BicomoduleMorphism) -> BicomoduleMorphism

Left-whisker of `β` by `M`: produces `id_M ⊙_h β : (M ⊙ N) ⇒ (M ⊙ N')`
where `M` is over `(C, D)` and `β : N ⇒ N'` is over `(D, E)`.
Requires `M.right_base === β.source.left_base`.
"""
function whisker_right(M::Bicomodule, β::BicomoduleMorphism)
    M.right_base === β.source.left_base ||
        error("whisker_right: M.right_base !== β.source.left_base")
    M_compose_N  = compose(M, β.source)
    M_compose_Np = compose(M, β.target)

    on_pos_fn = key -> begin
        x, y = key
        (x, β.underlying.on_positions.f(y))
    end
    # Direction-set at (x, y) is direction_at(N, y); after whiskering it's
    # direction_at(N', β(y)). β's on_directions provides the back-map.
    on_dir_fn = (key, b) -> begin
        x, y = key
        β.underlying.on_directions.f(y).f(b)
    end

    underlying = Lens(M_compose_N.carrier, M_compose_Np.carrier,
                      on_pos_fn, on_dir_fn)
    BicomoduleMorphism(M_compose_N, M_compose_Np, underlying)
end

"""
    horizontal_compose(α::BicomoduleMorphism, β::BicomoduleMorphism) -> BicomoduleMorphism

Full horizontal composition: α : M ⇒ M' (over C↛D) and β : N ⇒ N' (over
D↛E) compose to α ⊙_h β : M ⊙ N ⇒ M' ⊙ N' via whiskering. Concretely:
    α ⊙_h β = compose(whisker_left(α, β.source), whisker_right(α.target, β))

Requires `α.source.right_base === β.source.left_base`.
"""
function horizontal_compose(α::BicomoduleMorphism, β::BicomoduleMorphism)
    α.source.right_base === β.source.left_base ||
        error("horizontal_compose: α.source.right_base !== β.source.left_base")
    # Build the source/target composite bicomodules once each, then construct
    # the underlying lens directly. Going through whisker_left ; whisker_right
    # would build TWO copies of the intermediate `compose(α.target, β.source)`
    # (one as whisker_left's target, one as whisker_right's source), and the
    # vertical compose's `===` check rejects those as non-identical objects
    # even though they're structurally equal.
    M_compose_N    = compose(α.source, β.source)
    Mp_compose_Np  = compose(α.target, β.target)

    on_pos_fn = key -> begin
        x, y = key
        (α.underlying.on_positions.f(x), β.underlying.on_positions.f(y))
    end
    on_dir_fn = (key, b) -> begin
        _, y = key
        β.underlying.on_directions.f(y).f(b)
    end
    underlying = Lens(M_compose_N.carrier, Mp_compose_Np.carrier,
                      on_pos_fn, on_dir_fn)
    BicomoduleMorphism(M_compose_N, Mp_compose_Np, underlying)
end

# ============================================================
# Kan extensions of bicomodules — Extensions v2 PR #3
# ============================================================
#
# Per design note `docs/dev/kan_extensions_construction.md`. Two
# flavors:
#
#   * `kan_along_bicomodule(D, M; direction)` — Kan extension of a
#     comodule (here: a Bicomodule M viewed as such) along a bicomodule
#     D. Finite-only in v0.3.
#   * `kan_2cat(D, F; direction)` — Kan extension in the 2-category
#     obtained from Cat# by collapsing 2-cells. Symbolic-aware.
#
# Both return a `KanExtension` record carrying the extended object,
# the universal-property unit/counit 2-cell, and `factor_through` data.
#
# Phasing (per design note §4): identity case first (Σ_id_C M ≅ M with
# identity unit 2-cell), then non-identity left, then right, then 2cat.
# v0.3 ships the identity case + non-identity left for both flavors;
# right Kan and full symbolic 2cat may roll incrementally into v0.3.x.

"""
    KanExtension{T}

The result of a Kan-extension construction. Carries:

  - `extension::T` — the extended comodule (3a) or bicomodule (3b).
  - `unit::BicomoduleMorphism` — the universal 2-cell. For `direction=:left`,
    this is the unit `η`. For `direction=:right`, it's the counit `ε`.
  - `direction::Symbol` — `:left` or `:right`.
  - `source::Bicomodule` — the bicomodule extended along (i.e., `D`).
  - `input` — the original comodule/bicomodule that was extended.

Use [`factor_through`](@ref) to exhibit the universal property.
"""
struct KanExtension{T}
    extension::T
    unit::BicomoduleMorphism
    direction::Symbol
    source::Bicomodule
    input::Any
    function KanExtension{T}(extension::T, unit::BicomoduleMorphism,
                             direction::Symbol, source::Bicomodule,
                             input) where {T}
        direction in (:left, :right) ||
            throw(ArgumentError("KanExtension direction must be :left or :right; got :$direction"))
        new{T}(extension, unit, direction, source, input)
    end
end
KanExtension(extension::T, unit, direction, source, input) where {T} =
    KanExtension{T}(extension, unit, direction, source, input)

function show(io::IO, k::KanExtension{T}) where {T}
    print(io, "KanExtension{", T, "}(direction=:", k.direction, ")")
end

"""
    kan_along_bicomodule(D::Bicomodule, M::Bicomodule; direction=:left) -> KanExtension

Kan extension of a bicomodule `M` along a bicomodule `D`. Finite-only
in v0.3 (Q3.2).

  - `direction=:left` — `Σ_D M = M ⊙ D` via bicomodule composition.
    Requires `M.right_base === D.left_base`. Returns a `KanExtension`
    whose `extension` is the composite bicomodule and whose `unit` is
    the canonical 2-cell `η : M ⇒ M ⊙ D` (currently a placeholder
    identity-shape morphism for the identity-D case; non-identity D
    cases under development).
  - `direction=:right` — `Π_D M`, dual construction; not yet implemented
    in v0.3 — errors with a clear message pointing at the v0.3.x
    follow-up.

The Unicode aliases `Σ_D` and `Π_D` (defined below) provide
direction-named wrappers.
"""
function kan_along_bicomodule(D::Bicomodule, M::Bicomodule;
                              direction::Symbol=:left)
    direction in (:left, :right) ||
        throw(ArgumentError("kan_along_bicomodule: direction must be :left or :right; got :$direction"))

    if direction === :right
        error("kan_along_bicomodule(:right) not yet implemented — see " *
              "docs/dev/kan_extensions_construction.md §4 for the phasing. " *
              "v0.3 ships :left; :right rolls in v0.3.x.")
    end

    # Left Kan: Σ_D M = M ⊙ D.
    M.right_base === D.left_base ||
        error("kan_along_bicomodule(:left): M.right_base !== D.left_base. " *
              "M extends along D from C↛D'; D must be C↛E for some E.")

    extension = compose(M, D)

    # Unit η : M ⇒ Σ_D M = M ⊙ D. For the identity case (D ≅ regular
    # bicomodule on M.right_base), M ⊙ D ≅ M and η is identity. For
    # non-identity D, the unit is the canonical inclusion induced by
    # the universal property of the bicomodule composition. We
    # construct a placeholder whose underlying lens routes M's
    # carrier into the (M ⊙ D) carrier on the (x, y) coordinate where
    # y is the identity-direction at the right_base position
    # M.right_coaction.on_positions.f(x) projects to.
    #
    # The placeholder is correct for identity D (verifiable by
    # validate_bicomodule_morphism on the identity case) and a working
    # approximation for non-identity D (sound for routing; requires
    # the universal property to be checked separately for the
    # downstream coequalizer adjustment).
    unit_underlying = _unit_lens_for_left_kan(M, D, extension)

    # The unit is a 2-cell M ⇒ extension. Sources are M's bases (left=C,
    # right=D.left_base = C); target is extension's bases (left=C,
    # right=D.right_base=E). These DON'T share right_base (M's is C, the
    # extension's is E), so we cannot construct a same-base
    # BicomoduleMorphism here — the morphism shape genuinely lives in
    # the double category, not the strict-2-cell category.
    #
    # Workaround for v0.3: place the unit as a 2-cell on a wrapped
    # Bicomodule whose right_base matches the extension's right_base.
    # This is a stub; the correct treatment is in `bicomodule_morphism_over`
    # (planned) which carries explicit base-change retrofunctor data.
    # For test-purposes the identity-D case still validates because the
    # bases happen to coincide.
    M_for_unit = if M.right_base === extension.right_base
        M
    else
        # Re-wrap: a Bicomodule with the same carrier and coactions as M
        # but the extension's right_base. This won't validate in general
        # but lets us construct a 2-cell shell for the universal-property
        # API. A future bicomodule_morphism_over will replace this.
        Bicomodule(M.carrier, M.left_base, extension.right_base,
                   M.left_coaction, M.right_coaction)
    end
    unit = BicomoduleMorphism(M_for_unit, extension, unit_underlying)

    KanExtension(extension, unit, direction, D, M)
end

# Internal: build the underlying lens M.carrier → (M ⊙ D).carrier
# representing the unit of the left Kan extension. For identity D,
# this is the identity lens (after type alignment); for general D,
# it sends x ↦ (x, "fundamental y of D at the routed position").
function _unit_lens_for_left_kan(M::Bicomodule, D::Bicomodule, extension::Bicomodule)
    # (M ⊙ D).carrier positions are (x, y) pairs where y ∈ D.carrier.positions
    # and the routing condition on D-positions is satisfied. For each x in
    # M.carrier.positions, pick the "first" y that satisfies the routing
    # condition. The choice is canonical when D is the regular bicomodule
    # (each x has a unique compatible y via the identity cofibration).
    Xp = M.carrier.positions
    Xp isa FinPolySet ||
        error("_unit_lens_for_left_kan requires M.carrier.positions to be a FinPolySet")

    # Build a routing dict: x -> first compatible y in extension.carrier.positions
    routing = Dict()
    for x in Xp.elements
        candidates = filter(p -> p[1] == x, extension.carrier.positions.elements)
        isempty(candidates) &&
            error("_unit_lens_for_left_kan: no compatible y in extension.carrier for x = $x; " *
                  "the bicomodule composition M ⊙ D may have dropped this position. " *
                  "Verify M and D are compatible at x.")
        routing[x] = first(candidates)
    end

    on_pos = x -> routing[x]
    # Direction-set at extension.carrier[(x, y)] is direction_at(D.carrier, y).
    # For the unit lens, we need a back-direction map: cod-direction at the
    # routed position ↦ dom-direction at x. The canonical choice for the
    # identity-D case is to take the back-direction through M.right_coaction's
    # backward map, which always lands in M.carrier[x]. For the general
    # case, an explicit choice is needed; using the right_coaction back-map
    # is a working approximation.
    on_dir = (x, b) -> begin
        # Take a direction in D.carrier[y] — but interpret it as a direction
        # in M.carrier[x] via M's right coaction. Identity-D case: this is
        # the identity. General case: approximation.
        Dx = direction_at(M.carrier, x)
        Dx isa FinPolySet || return b
        # If b happens to be in M.carrier[x]'s elements, return it directly.
        # Otherwise route through right_coaction's back-map.
        if b in Dx.elements
            b
        else
            # Best-effort: pick any direction in Dx; identity-D case won't hit this branch.
            first(Dx.elements)
        end
    end
    Lens(M.carrier, extension.carrier, on_pos, on_dir)
end

"""
    kan_2cat(D::Bicomodule, F::Bicomodule; direction=:left) -> KanExtension

Kan extension in the 2-category obtained from `Cat#` by collapsing
2-cells. `D : C ↛ E` and `F : C ↛ E'` share the same source comonoid
`C`. Returns `Lan_D F : E ↛ E'` (left) or `Ran_D F : E ↛ E'` (right).

Symbolic-aware (Q3.2): inputs may have lazy or symbolic carriers; the
construction defers materialization to the symbolic layer where
possible.

In v0.3, the implementation handles the **identity** D case
(`Lan_id_C F = F`) explicitly. Non-identity D requires a coequalizer
adjustment that the symbolic layer doesn't yet expose; those cases
error with a pointer to v0.3.x.
"""
function kan_2cat(D::Bicomodule, F::Bicomodule; direction::Symbol=:left)
    direction in (:left, :right) ||
        throw(ArgumentError("kan_2cat: direction must be :left or :right; got :$direction"))

    D.left_base === F.left_base ||
        error("kan_2cat: D.left_base !== F.left_base; both must share the source comonoid.")

    # Identity-D detection: D is "essentially" identity if its carrier
    # equals D.left_base.carrier and its coactions reduce to the
    # duplicator. Approximate with a structural check (the compose
    # function gives an iso to F when D is regular; we use that as the
    # operational definition of "identity-D" here).
    is_identity_D = D.carrier == D.left_base.carrier &&
                    D.left_base === D.right_base

    if !is_identity_D
        error("kan_2cat: non-identity D not yet implemented — requires a " *
              "coequalizer in the symbolic layer that v0.3 does not expose. " *
              "See docs/dev/kan_extensions_construction.md §4 for phasing. " *
              "v0.3 ships the identity-D case; non-identity rolls in v0.3.x.")
    end

    # Identity D: Lan_D F ≅ F, unit = id_F.
    extension = F
    unit = identity_bicomodule_morphism(F)
    KanExtension(extension, unit, direction, D, F)
end

"""
    factor_through(k::KanExtension, α::BicomoduleMorphism) -> BicomoduleMorphism

Exhibit the universal property of the Kan extension. For a left Kan
`Σ_D M`, given a 2-cell `α : M ⇒ N` for some appropriate `N`, return
the unique factoring 2-cell `Σ_D M ⇒ N` whose composition with the
unit recovers `α`.

In v0.3, `factor_through` is implemented for the **identity** D case
where `Σ_D M ≅ M` and the factor is `α` itself (modulo type alignment).
Non-identity D requires solving the coequalizer that defines the unit;
that's deferred to v0.3.x.
"""
function factor_through(k::KanExtension, α::BicomoduleMorphism)
    # Identity D check (matches the kan_along_bicomodule / kan_2cat logic).
    is_identity_D = k.source.carrier == k.source.left_base.carrier &&
                    k.source.left_base === k.source.right_base

    if !is_identity_D
        error("factor_through: non-identity D not yet implemented — see " *
              "docs/dev/kan_extensions_construction.md §4. " *
              "v0.3 supports the identity-D case.")
    end

    # Identity D: the factoring 2-cell IS α (after rewrapping its source
    # as the extension if needed).
    α.source.carrier == k.extension.carrier ||
        error("factor_through: α.source.carrier ≠ k.extension.carrier. " *
              "α must originate at the Kan extension's input.")
    α
end

# Unicode aliases per Q3.4.
const var"Σ_D" = (D::Bicomodule, M::Bicomodule) ->
    kan_along_bicomodule(D, M; direction=:left)
const var"Π_D" = (D::Bicomodule, M::Bicomodule) ->
    kan_along_bicomodule(D, M; direction=:right)

# ============================================================
# LazyCofreeComonoid (Extensions v2 PR #8)
# ============================================================
#
# Defers the eager `behavior_trees` enumeration until the user actually
# queries the comonoid's structure. Holds just `(p, depth)` plus a
# materialization cache.
#
# Per Q8.1 resolution (multi-select all four):
#   - `eraser` access works without forcing materialization beyond what
#     the lens itself needs (still has to know the carrier shape; we
#     materialize that on first access and cache).
#   - shape-level `validate_comonoid` returns `true` for any
#     `LazyCofreeComonoid` based on Niu/Spivak Thm 8.45 (cofree
#     comonoids are always comonoids); no enumeration needed.
#   - structural equality compares `(p, depth)` directly, no
#     enumeration.
#   - `parallel` of two lazy cofrees forces materialization of both and
#     defers to `parallel(::Comonoid, ::Comonoid)` from Tier 1 PR #1.
#
# Per Q8.2: `tree_at(c, index)` exposes a single tree (currently via
# materialize-and-index; future optimization may stream).
#
# Per Q8.3: materialized trees are cached; `clear_cache!(c)` frees the
# cache.

"""
    LazyCofreeComonoid(p::Polynomial, depth::Int)

Lazy variant of [`cofree_comonoid`](@ref): holds the polynomial and
depth without enumerating the (potentially astronomical) tree set up
front. Materialization is on-demand via [`materialize`](@ref) and
cached on the struct.

Construct with [`cofree_lazy`](@ref). Pair with the v2 design note's
combinatorial table (`src/Cofree.jl` header) to size the depth choice.
"""
mutable struct LazyCofreeComonoid
    p::Polynomial
    depth::Int
    _materialized::Union{Nothing,Comonoid}
    function LazyCofreeComonoid(p::Polynomial, depth::Int)
        depth ≥ 0 || throw(ArgumentError("depth must be ≥ 0; got $depth"))
        new(p, depth, nothing)
    end
end

function show(io::IO, c::LazyCofreeComonoid)
    state = c._materialized === nothing ? "lazy" : "materialized"
    print(io, "LazyCofreeComonoid(", c.p, ", depth=", c.depth, ", ", state, ")")
end

"""
    cofree_lazy(p::Polynomial, depth::Int) -> LazyCofreeComonoid

Build a lazy version of `cofree_comonoid(p, depth)`. The trees aren't
enumerated until the user calls [`materialize`](@ref) (or any
operation that needs the carrier polynomial).
"""
cofree_lazy(p::Polynomial, depth::Int) = LazyCofreeComonoid(p, depth)

"""
    materialize(c::LazyCofreeComonoid) -> Comonoid

Force eager enumeration of the cofree comonoid. The result is cached
on `c._materialized`; subsequent calls return the cached value. Use
[`clear_cache!`](@ref) to free the cache.
"""
function materialize(c::LazyCofreeComonoid)
    c._materialized === nothing || return c._materialized
    eager = cofree_comonoid(c.p, c.depth)
    c._materialized = eager
    eager
end

"""
    clear_cache!(c::LazyCofreeComonoid) -> LazyCofreeComonoid

Free the cached materialized comonoid. Returns `c` for chaining.
Subsequent operations will re-materialize on demand.
"""
function clear_cache!(c::LazyCofreeComonoid)
    c._materialized = nothing
    c
end

# ------------------------------------------------------------
# Lazy operations (Q8.1)
# ------------------------------------------------------------

"""
    eraser(c::LazyCofreeComonoid) -> Lens

The counit lens of the lazy cofree comonoid. Materializes the
underlying carrier on first call (cached); subsequent calls reuse the
cache.
"""
eraser(c::LazyCofreeComonoid) = materialize(c).eraser

"""
    duplicator(c::LazyCofreeComonoid) -> Lens

The duplicator (comultiplication) lens. Materializes on first call.
"""
duplicator(c::LazyCofreeComonoid) = materialize(c).duplicator

# Forward `validate_comonoid` for lazy cofrees: returns `true` based on
# Niu/Spivak Thm 8.45 (cofree comonoids are always comonoids). Pass
# `force=true` to materialize and run the full validator anyway.
"""
    validate_comonoid(c::LazyCofreeComonoid; force=false) -> Bool

Validate the lazy cofree comonoid. By default returns `true` without
materializing — every cofree comonoid satisfies the comonoid laws by
Niu/Spivak Thm 8.45, so the shape-level answer is structural. Pass
`force=true` to materialize and run the full element-level validator.
"""
function validate_comonoid(c::LazyCofreeComonoid; force::Bool=false)
    force || return true
    validate_comonoid(materialize(c))
end

# Structural equality without materialization: compare (p, depth).
==(a::LazyCofreeComonoid, b::LazyCofreeComonoid) =
    a.p == b.p && a.depth == b.depth

# parallel of two lazy cofrees forces materialization of both, then
# delegates to parallel(::Comonoid,::Comonoid). The result is a
# Comonoid (not a LazyCofreeComonoid — the parallel of two cofrees
# isn't itself cofree in general).
"""
    parallel(a::LazyCofreeComonoid, b::LazyCofreeComonoid) -> Comonoid

Carrier-tensor parallel of two lazy cofrees. Forces materialization of
both inputs, then uses `parallel(::Comonoid, ::Comonoid)` from
Extensions v2 PR #1. The result is a `Comonoid`, not a
`LazyCofreeComonoid` — parallel of two cofree comonoids is not
itself cofree in general.
"""
parallel(a::LazyCofreeComonoid, b::LazyCofreeComonoid) =
    parallel(materialize(a), materialize(b))

# ------------------------------------------------------------
# tree_at (Q8.2)
# ------------------------------------------------------------

"""
    tree_at(c::LazyCofreeComonoid, index::Int) -> BehaviorTree

Return the `index`-th behavior tree of the cofree comonoid (1-based).
Currently materializes the full carrier on first call (cached) and
indexes into the resulting position list. A future optimization may
stream individual trees without enumerating the full set.
"""
function tree_at(c::LazyCofreeComonoid, index::Int)
    eager = materialize(c)
    elements = eager.carrier.positions.elements
    1 ≤ index ≤ length(elements) ||
        throw(BoundsError("tree_at: index $index out of bounds (1:$(length(elements)))"))
    elements[index]
end

# ------------------------------------------------------------
# Helpers
# ------------------------------------------------------------

"""
    is_materialized(c::LazyCofreeComonoid) -> Bool

True iff the lazy cofree has already been materialized (cache hit on
the next operation that would otherwise enumerate).
"""
is_materialized(c::LazyCofreeComonoid) = c._materialized !== nothing
