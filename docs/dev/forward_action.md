# Forward direction action on `Retrofunctor` (companion note)

> **Status**: dev note for v0.4.x forward-action patch (`base_change_*`
> dispatch, populated `forward_on_directions` on `cofree_morphism` and
> `tuple_retrofunctor` and `compose`) and the v0.5 follow-up
> (`validate_retrofunctor_forward`). Both patches share an architectural
> seam — the optional `forward_on_directions` field on `Retrofunctor`
> — but address different consumer surfaces. This note collects the
> "when do I use which validator / which API path" guidance in one place.

---

## 1. Two natural direction actions

A retrofunctor `F : C → D` (= functor between the corresponding
categories per Ahman–Uustalu) has two natural direction actions.

  - **Backward**, in `F.underlying.on_directions`. At each
    `c0 ∈ dom-positions`, given a cod-direction at `F(c0)`, return the
    corresponding dom-direction. Always stored — it is the on-directions
    component of the underlying `Lens`. **Total** only when `F`'s image
    is the full codomain. **Partial** otherwise.
  - **Forward**, in the optional `forward_on_directions` field. At each
    `c0 ∈ dom-positions`, given a dom-direction at `c0`, return the
    corresponding cod-direction at `F(c0)`. Populated by constructors
    that can compute it canonically.

### Constructors that populate `forward_on_directions`

  - `identity_retrofunctor(c)` — forward = identity.
  - `compose(F, G)` — forward of the composite when both `F` and `G`
    carry forward; else `nothing`.
  - `cofree_morphism(L, depth)` — forward is the
    "filter-subsequence" derived from the back-action `L`'s direction
    inclusion.
  - `tuple_retrofunctor([F_d])` — forward is the per-component tuple
    `(F_1.forward, …, F_n.forward)` left-folded.

### Partial-image retrofunctors

When the back-action `F.underlying.on_directions` is undefined on
non-image cod-directions, we call `F` a **partial-image retrofunctor**.
Two canonical sources:

  - `cofree_morphism(L, depth)` over a non-identity boundary lens: the
    back-action is `L`'s direction inclusion's preimage. Defined on the
    image of the inclusion, undefined elsewhere.
  - `tuple_retrofunctor([F_d])` over a non-trivial compatible family:
    the back-action's agreement check passes only on tensored
    direction tuples in the diagonal image. On non-image tuples the
    components disagree by design and the runtime errors with a clear
    "components disagree on direction lift" message.

Partial-image retrofunctors are categorically valid functors. They
satisfy the comonoid-morphism axioms. They just can't witness the
axioms via their back-action because the back-action isn't asked
totally-defined questions.

---

## 2. Cat# operations: `base_change_left` / `base_change_right`

Patched in v0.4.x. Both functions check `F.forward_on_directions !==
nothing`; if so, they dispatch to a forward-iteration helper that walks
dom-directions and applies `F.forward` instead of inverting `F.on_directions`
over cod-directions. The forward path:

  - Drops the `F.on_directions` injectivity precondition (irrelevant
    when we don't invert).
  - Succeeds on partial-image retrofunctors that the backward path
    would error on (non-image cod-directions are simply never visited).
  - Produces the same bicomodule as the backward path on cases where
    both apply.

Position-injectivity is still required (and checked eagerly) on both
paths — that is a Cat# precondition, not an artifact of the back-action.

## 3. Self-validation: `validate_retrofunctor_forward`

Patched in v0.5. The existing `validate_retrofunctor(F; strict=true)`
and `strict=false` modes both probe `F.underlying.on_directions` on
every cod-direction at every position. They cannot validate
partial-image retrofunctors — the same agreement-check error that
`base_change_left`'s backward path hit will surface here too.

`validate_retrofunctor_forward(F)` checks comonoid-morphism axioms via
`F.forward_on_directions`, never touching `on_directions`. Element-wise
checks:

  - **Counit preservation.** `F.forward(c0).f(id_dom_at_c0) ==
    id_cod_at_F(c0)` for every dom-position `c0`.
  - **Comult preservation (composition law).** For every
    `(c0, b, b')` with `b ∈ C[c0]` and `b' ∈ C[jbar_dom(c0)[b]]`:
    `F.forward(c0).f(b ;_dom b') == F.forward(c0).f(b) ;_cod
     F.forward(c0').f(b')`
    where `;_dom` and `;_cod` are the respective duplicators'
    on-directions composition. Equivalently: `F.forward` is a
    monoid-morphism of "morphism algebras". For cofree comonoids
    `;_dom` and `;_cod` are path concatenation, so this reads "forward
    respects path concatenation" — the property that makes
    `cofree_morphism`'s filter-subsequence a valid retrofunctor's
    morphism action.

### Why no position-side check

A naive forward translation of comult would also check
`F(c0') == jbar_cod(F(c0))[F.forward(c0).f(b)]`. **This does not hold**
on `cofree_morphism(L, depth)` over a non-identity alphabet-inclusion
`L`, even though that morphism strict-validates as a back-action
retrofunctor. A dom-direction outside `L`'s image is filtered to the
identity cod-direction `()`, whose cod-codomain is `F(c0)` itself —
but `F(c0')` is a strictly deeper subtree.

The position-side equation characterizes retrofunctors whose forward
action is the morphism action of a strict functor with bijective
direction routing. It is too strong as an invariant of "valid
retrofunctor". Counit + composition law is what's actually invariant
across the constructions that populate `forward_on_directions`.

### When to use which validator

| Retrofunctor shape                                | Validator                                                  |
|---------------------------------------------------|------------------------------------------------------------|
| Total back-action (identity, free composition)    | `validate_retrofunctor(F)` — strict or element-wise        |
| Forward populated, back-action total              | Either; forward is faster on large cod-direction sets      |
| Partial-image (tuple-of-cofree-morphisms etc.)    | `validate_retrofunctor_forward(F)` — mandatory             |
| Cofree-universal truncation                       | Neither: verify universal property directly (existing note in `validate_retrofunctor` docstring) |

## 4. Architectural symmetry

`base_change_left` (v0.4.x) and `validate_retrofunctor_forward` (v0.5)
are the two consumers of `forward_on_directions`. They share a single
dispatch convention: **if `F.forward_on_directions !== nothing`, the
forward path is the applicable one**. Constructors populate the field
canonically; downstream code dispatches on its presence. No global
config, no opt-in flag.

This convention extends naturally to any future Cat#-machinery that
needs to walk a retrofunctor's direction action. Add the
`F.forward_on_directions !== nothing` check, write the forward variant
alongside the backward one, dispatch.
