# Cofree comonoid on a comonoid (companion note)

> **Status**: design note for Poly.jl v0.4 #4. Written before
> implementation per Q4.1 in `extensions_v3_design.md`.

This note pins down what `cofree_comonoid(c::Comonoid, depth::Int)`
constructs, what universal property it exhibits, and what
`factor_through` of the result actually computes. It exists because the
v2 deferral of #13 was driven by the fuzziness of "the universal property
of the cofree comonoid on a comonoid" — doing it half-right would be
worse than skipping. Writing this down gates the implementation.

---

## 1. What's already in v0.3 — cofree on a polynomial

`cofree_comonoid(p::Polynomial, depth::Int)` (Sprint 8, refined through
v0.3) builds the depth-bounded cofree comonoid `T_p` on a *polynomial*
`p`. Niu/Spivak Ch. 8: `T_p` is the right adjoint to the forgetful
functor `Cat# → Poly` carrying a small category to its underlying
polynomial.

Operationally the depth-`d` truncation has trees-of-depth-≤-`d` as
positions, with paths-into-trees as directions. The comonoid laws hold
exactly in the truncation. The universal property holds *element-wise*
(per `validate_retrofunctor(F; strict=false)`) — a c-walk of length `k`
lands on a depth-(d-k) tree, while `(F ▷ F) ∘ c.duplicator` lands on a
fresh depth-`d` tree, so strict equality fails for the truncation.

That's the *cofree-on-a-polynomial* story. v0.4 #4 is a different beast.

---

## 2. What v0.4 #4 builds — cofree on a *comonoid*

The cofree-on-a-comonoid `T(c)` is **not** simply `T_(c.carrier)` with
extra structure. The right thing sits at the level of *comodules*: given
a comonoid `c`, we want a cofree comonoid `T(c)` with a universal
counit `T(c) ⇒ c` (a 2-cell of comonoids / equivalently a retrofunctor)
through which any comonoid morphism `D ⇒ c` factors.

The closest book reference is the ∗-bifibration discussion in Ch. 8 — the
construction lives where comonoid morphisms (= retrofunctors of
categories) and comodules (= prafunctors) meet.

### 2.1 Why this is fuzzy

Three sources of fuzziness:

1. **Uniqueness up to what?** The universal property names a unique
   factorization, but uniqueness in `Cat#` is up to *equivalence of
   retrofunctors*, not equality of underlying lenses. Our existing
   `validate_retrofunctor(F; strict=false)` already needs the
   element-wise convention; the cofree-on-a-comonoid factorization
   inherits the same.

2. **Truncation-vs-limit.** As with `cofree(p, d)`, finite depth
   truncates an inherently infinite construction. The truncated
   `T_(d)(c)` factors element-wise but not strictly. v0.5+ may add a
   lazy/coinductive variant.

3. **Underlying carrier.** Two conventions appear in the literature:
   (a) trees over `c.carrier` augmented with composition-history,
   (b) limits of finite quotients. They produce the same cofree object
   up to equivalence but materialize different finite truncations. v0.4
   commits to (a) because it reuses `cofree(::Polynomial, depth)`'s
   tree-enumeration machinery.

### 2.2 The construction (v0.4)

Given `c::Comonoid` and `depth::Int`:

1. Build the underlying tree-comonoid on the polynomial `c.carrier`:
   `Tp = cofree_comonoid(c.carrier, depth)`. This is the v0.3
   cofree-on-polynomial.
2. Augment with a *counit* `Retrofunctor : Tp ⇒ c`. The counit's
   underlying lens is exactly `cofree_unit(c.carrier, depth)` — a
   `Lens` whose on-positions strips a tree to its root and whose
   on-directions sends a `c`-direction `a` to the singleton path
   `(a,)`. Wrapping in `Retrofunctor` records that the morphism
   respects the comonoid structure (element-wise; see §2.1).
3. The result is a record:

   ```julia
   struct CofreeOverComonoid
       base::Comonoid
       depth::Int
       cofree::Comonoid               # = Tp from step 1
       counit::Retrofunctor     # Tp ⇒ c structurally
   end
   ```

The counit witnesses what's universal: any comonoid morphism `D ⇒ c`
factors through `counit` element-wise.

### 2.3 What `factor_through(coc, α)` exhibits

Given `coc::CofreeOverComonoid` (with `coc.base === c`) and a
`α::Retrofunctor` of shape `D ⇒ c`, `factor_through` returns the
unique `β : D ⇒ coc.cofree` whose composition with `coc.counit` recovers
`α`:

```
   β              counit
D ───→ coc.cofree ────→ coc.base    =    α : D ⇒ coc.base   (element-wise)
```

Implementation note: `α : D ⇒ c` is a comonoid morphism (= retrofunctor),
which means `α.underlying` is a `Lens` from `D.carrier` to `c.carrier`.
The cofree-on-polynomial helper `cofree_universal(D, α.underlying, depth)`
already builds the unique structural retrofunctor `D ⇒ T_(c.carrier)`
that factors a labeling through the depth-`depth` tree comonoid. We
delegate to it.

The element-wise convention applies — the round-trip
`compose(β, counit) ≈ α` holds at every `D`-position but not necessarily
under strict `Lens ==`. Same caveat as `cofree_universal`'s
`strict=false` path. Documented in the docstring.

### 2.4 What `factor_through` does NOT exhibit

- **Strict uniqueness.** Two element-wise-equal `β`s may differ
  structurally in the lens representation; we return one canonical
  choice.
- **Lazy / infinite cofree.** Truncation at `depth` means the universal
  property holds only for `D`-walks of length ≤ `depth`. Deeper walks
  are silently truncated; users must pick `depth` large enough for their
  use case.

---

## 3. API shape

```julia
"""
    cofree_comonoid(c::Comonoid, depth::Int) -> CofreeOverComonoid

The depth-`depth` cofree comonoid on `c`. ...
"""
function cofree_comonoid(c::Comonoid, depth::Int) :: CofreeOverComonoid

"""
    factor_through(coc::CofreeOverComonoid, α::Retrofunctor;
                   strict::Bool=false) -> Retrofunctor

The unique `β : α.dom ⇒ coc.cofree` whose composition with
`coc.counit.underlying` equals `α.underlying` element-wise. Delegates to
[`cofree_universal`](@ref) under the hood.
"""
function factor_through(coc::CofreeOverComonoid, α::Retrofunctor;
                        strict::Bool=false) :: Retrofunctor
```

`strict=true` runs the `validate_bicomodule_morphism` round-trip check
on `compose(β, counit)` against `α` and errors on mismatch; `false`
(default per Q4.2) trusts the element-wise construction.

The function name `cofree_comonoid` is overloaded with the existing
`cofree_comonoid(::Polynomial, ::Int)` — Julia's multiple dispatch
disambiguates by the first argument's type.

---

## 4. Out of scope for v0.4

- **Lazy cofree-on-comonoid.** The mirror of #8 from v2 (lazy cofree on
  polynomial). Defer to v0.5 unless modeling needs surface.
- **Continuous-depth limit.** The colimit-over-depth construction is
  cleaner mathematically but harder to materialize.
- **Symbolic comonoids.** When `c.carrier.positions` is non-finite, we'd
  need symbolic-tree machinery. Defer; same hooks as the symbolic
  `kan_2cat` path can be reused later.

---

## 5. Test plan

- `cofree_comonoid(c, depth)` returns a `CofreeOverComonoid` whose
  `cofree` is a valid `Comonoid` (`validate_comonoid` passes).
- The counit composes correctly on identities: `counit ⨟ id_c ≈ counit`.
- `factor_through(coc, identity_bicomodule_morphism(c))` returns
  something whose composition with the counit equals the identity 2-cell
  on `c`, element-wise.
- Comparison with `cofree(eraser_only_comonoid, d)` (Niu/Spivak's case
  where the comonoid is just a discrete one) agrees with the v2
  `cofree(p, d)` on the underlying carrier polynomial.
- Adversarial: depth-0 produces a trivial cofree; depth-1 gives one
  tree level; depth-`d` recovers the same tree count as
  `_trees_at_depth(c.carrier, d)`.
