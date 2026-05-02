# Poly.jl — Extensions v2 Design Doc

> **Status**: design signed off 2026-05-01. All open questions resolved (see §17). Implementation may proceed per the release plan in §16.
>
> Drafted from a structured feedback document by the same external user who drove Extensions v1, after building **Sequences 1–4** of a downstream PolyCDS application on v0.2.0. Fifteen items grouped into four classes: blockers (the ones that gate the next sequences), authoring quality-of-life, documentation, and smaller niceties. Reviewer commentary preserved verbatim where load-bearing.

---

## 0. Summary

| # | Item | Class | Breaks API? | PR size | Depends on |
|---|---|---|---|---|---|
| 1 | `parallel(::Comonoid, ::Comonoid)` carrier-tensor (and `⊗` semantics fix) | Blocker | **Soft** (⊗ deprecation) | S | — |
| 2 | First-class `BicomoduleMorphism` (2-cells) **+ horizontal composition** | Blocker | No (additive) | XL | — |
| 3 | Kan extensions: `kan_along_bicomodule` (finite) **+** `kan_2cat` (symbolic-aware), with `KanExtension` record | Blocker | No (additive) | XL | #2 |
| 4 | `support(X, φ)` (Fairbanks-style) **including symbolic** | Blocker | No (additive) | L | — |
| 5 | `bicomodule_from_data` **+ `comonoid_from_data`** | QoL | No (additive) | M | — |
| 6 | `back_directions` accessor + `BackDirectionTable` struct + `sharp_L`/`sharp_R` | QoL | No (additive) | S | — |
| 7 | `minimal_failing_triple` worked-example docstring | QoL / Docs | No | XS | — |
| 8 | Lazy `cofree_comonoid` with full lazy-comonoid algebra (eraser, validate, equality, parallel) | QoL | No (additive) | L | — |
| 9 | `validate_bicomodule_detailed` — explicit axiom listing | Docs | No | XS | — |
| 10 | Cofree depth tradeoff — formula + table (numerically verified) | Docs | No | XS | — |
| 11 | Worked-example bicomodule walkthrough doc | Docs | No | M | #1, #2, #5 |
| 12 | `representable(::Vector)` overload | Nice | No (additive) | XS | — |
| 13 | `cofree_comonoid(::Comonoid, depth)` — **deferred to Extensions v3** | — | — | — | — |
| 14 | `free_category_comonoid(vertices, edges)` with depth-bounded handling of cycles | Nice | No (additive) | S | — |
| 15 | `@poly` macro — examples surfaced in docs | Docs | No | XS | — |

**Phasing** — single v0.3.0 release bundling everything (per Q-resolution 2026-05-01):

- **Tier 0 (mechanical, can land in parallel):** #12, #7, #9, #10, #14, #15.
- **Tier 1 (Sequence 1 unblock):** #1.
- **Tier 2 (Sequence 2 unblock):** #6 → #5 → #2 (with horizontal composition).
- **Tier 3 (Sequence 3 unblock):** #3 (split internally into 3a finite kan_along_bicomodule + 3b symbolic-aware kan_2cat, but ships in one release).
- **Tier 4 (Sequence 4 unblock):** #4 (concrete + symbolic in one PR).
- **Tier 5:** #8 (lazy cofree with full lazy-comonoid algebra), #11 (walkthrough doc).
- **Deferred to v3:** #13.

**Where the codebase stands today.** Extensions v1 shipped as v0.2.0: lazy substitution, monoidal operators on `Comonoid`/`Bicomodule`, n-ary coproduct, structural-validation diagnostics with `minimal_failing_triple`, symbolic interop polish. The v2 work is largely about (a) closing categorical gaps the audit confirmed are missing — bicomodule morphisms, Kan extensions, supports — and (b) reducing the cost of authoring and debugging non-trivial bicomodules. Items #1, #5, #6, #7 grew out of the reviewer hand-rolling code in `ProtocolCompileV2.jl` that should have been one library call.

**Audit note (load-bearing for #1).** `Comonoid.jl:383–396` exports `⊗(::Comonoid, ::Comonoid)` and delegates to categorical product `*`. This is a naming inconsistency with `Polynomial`, where `*` is product and `⊗` is the Dirichlet tensor. The reviewer's request for `parallel(::Comonoid, ::Comonoid)` is asking for the carrier-tensor that `_comonoid_carrier_tensor` (`Cofree.jl:1101`) already implements internally. See §1 for proposed resolution.

---

## 1. `parallel(::Comonoid, ::Comonoid)` carrier-tensor (and `⊗` semantics fix)

**Problem.** Sequence 1 of the downstream PolyCDS work needs the joint comonoid `P = ⊗_d P_d` formed by tensoring per-disease carrier polynomials. The carrier-tensor construction exists internally as `_comonoid_carrier_tensor(c, d)` (`Cofree.jl:1101–1139`) — used inside `parallel(::Bicomodule, ::Bicomodule)` (`Cofree.jl:1162`) — but is never exported. Hand-building the equivalent reaches into `SmallCategory` and reinvents what `_comonoid_carrier_tensor` already does correctly.

Compounding this: `⊗(::Comonoid, ::Comonoid)` IS exported (`Comonoid.jl:383–396`), but it delegates to `c * d` (categorical product). On `Polynomial`, `*` is product and `⊗` is the Dirichlet tensor — so the current `Comonoid` definition of `⊗` is inconsistent with the rest of the type tower. Users following the polynomial naming pattern (and the reviewer in particular) will reach for `⊗` expecting carrier-tensor and get categorical product instead, silently.

### 1.1 Proposed design

**Two changes, one PR:**

1. Add `parallel(::Comonoid, ::Comonoid) -> Comonoid` as the public surface of what is currently `_comonoid_carrier_tensor`. Move the implementation from `Cofree.jl` to `Comonoid.jl` (its semantic home) and have `parallel(::Bicomodule, ::Bicomodule)` call the public version. Keep the underscore-prefixed internal name as a `const` alias for one minor version, then drop it.

2. Realign `⊗(::Comonoid, ::Comonoid)` to mean carrier-tensor (i.e., `parallel`), matching `⊗(::Polynomial, ::Polynomial)` semantics. The current `*(::Comonoid, ::Comonoid) -> Comonoid` (categorical product) stays at `*`. This is a soft API break for any caller relying on `⊗` to mean product on comonoids.

```julia
# Public surface after #1:
parallel(c::Comonoid, d::Comonoid)  :: Comonoid     # carrier ⊗ on Polynomial
⊗(c::Comonoid, d::Comonoid)         :: Comonoid     # alias for parallel (semantics fix)
*(c::Comonoid, d::Comonoid)         :: Comonoid     # categorical product (unchanged)
+(c::Comonoid, d::Comonoid)         :: Comonoid     # disjoint union (unchanged)
```

### 1.2 Resolutions (2026-05-01)

- **Q1.1 — Hard break in v0.3 (revised from soft).** Originally resolved as "soft break with deprecation warning across one minor; v0.4 flips `⊗` semantics." During implementation we discovered that `Monoidal.jl` defines `const var"⊗" = parallel`, making `⊗` and `parallel` literally the same Julia function — adding a method to one IS adding a method to the other; they cannot disagree for the same argument types. The original soft-break plan was therefore structurally impossible. Re-resolved 2026-05-01 to do the v0.4 flip immediately in v0.3: `⊗(c::Comonoid, d::Comonoid)` ≡ `parallel(c::Comonoid, d::Comonoid)` ≡ carrier-tensor. Migration note: v0.2 callers who used `c ⊗ d` for the categorical product must switch to `c * d`.
- **Q1.2 — Validate at construction.** `parallel(::Comonoid, ::Comonoid)` runs the full comonoid coherence checks (counit + coassoc) on the result. Belt-and-suspenders against any latent bugs in the existing `_comonoid_carrier_tensor`. Cost is acceptable since this is a construction-time, not hot-path, operation.

### 1.3 Out of scope for #1

- N-ary `parallel(::Comonoid...)` and `⊗(::Comonoid...)` variants. Easy to add once the binary form is settled; defer to a follow-up if the reviewer's downstream uses `parallel(P_d for d in diseases...)` syntax.

### 1.4 Tests

- Carrier polynomial of `parallel(c, d)` equals `c.carrier ⊗ d.carrier` structurally.
- Round-trip: building a `Bicomodule` over `parallel(c, d)` as a left base via the new public function gives the same object as v0.2.0's internal path.
- Eraser and duplicator of `parallel(c, d)` validate as a comonoid.

---

## 2. First-class `BicomoduleMorphism` (2-cells)

**Problem.** Sequence 2's "A as 2-cell family" construction needs morphisms between bicomodules — the 2-cells of the double category Cat# of comonoids/bicomodules. The audit confirmed: no such struct exists. `Lens` is for polynomial morphisms, `Retrofunctor` is for comonoid morphisms (1-cells in the wrong direction for our purposes), but there is no "morphism between bicomodules over the same pair of bases."

The reviewer's proposed shape: `(source::Bicomodule, target::Bicomodule, underlying::Lens)` plus a constraint that the underlying lens respects both coactions.

### 2.1 Proposed design

```julia
"""
    BicomoduleMorphism(source::Bicomodule, target::Bicomodule, underlying::Lens)

A 2-cell α : source ⇒ target between two bicomodules sharing the same
left and right base comonoids. `underlying` is a polynomial lens
`source.carrier → target.carrier` whose composition with each coaction
of `source` agrees with the corresponding coaction of `target`.

Coherence (validated at construction):
  - `target.left_coaction ⊙ underlying  ==  (id_L ▷ underlying) ⊙ source.left_coaction`
  - `target.right_coaction ⊙ underlying ==  (underlying ▷ id_R) ⊙ source.right_coaction`

where `⊙` is lens composition and `▷` is `subst` on lenses.
"""
struct BicomoduleMorphism
    source::Bicomodule
    target::Bicomodule
    underlying::Lens
end
```

Construction enforces (a) source/target share `left_base` and `right_base` (object-identical, not just structurally equal — to keep this cheap), and (b) the two coherence squares commute, deferring to lazy lens-equality where possible.

**Companion API:**

```julia
identity_bicomodule_morphism(B::Bicomodule)     :: BicomoduleMorphism
compose(α, β)                                    :: BicomoduleMorphism   # vertical composition
validate_bicomodule_morphism(α::BicomoduleMorphism)         :: Bool
validate_bicomodule_morphism_detailed(α)                    :: ValidationResult
```

Vertical composition is defined when `α.target === β.source`. **Horizontal composition is in scope** (per Q2.2 resolution).

### 2.2 Resolutions (2026-05-01)

- **Q2.1 — Identity (`===`).** Source/target must share base comonoids by object identity. Cheap, unambiguous, matches how downstream code threads `Comonoid` objects through bicomodules in practice. A separate `bicomodule_morphism_over` constructor with retrofunctor mediators handles different-base 2-cells if/when needed.
- **Q2.2 — Horizontal composition included in #2.** The full double-category 2-cell story ships in this PR. This expands #2 from L to **XL**: in addition to vertical composition (`α.target === β.source`), the PR adds horizontal composition (whiskering and 2-cell composition in the double category Cat#), which interacts with retrofunctors and base-change. Sub-design will be in `docs/dev/bicomodule_2cells_construction.md` accompanying the PR.
- **Q2.3 — Mirror `ValidationResult` exactly.** `validate_bicomodule_morphism_detailed` returns a `ValidationResult` with `.passed`, `.failures`, `.summary`, compatible with `minimal_failing_triple`. Especially important now that horizontal composition adds new coherence axioms beyond the two coaction-respect squares — uniform return type lets debugging tooling generalize.
- **Q2.4 — Use `is_subst_of` style lazy equality, fall back as needed.** Coherence checks reach for lazy structural equality first (mirroring how Extensions v1 #1 fixed `subst` equality). If a specific case forces materialization, surface it at PR time as a depends-on against the v1.1 lazy-`Lens.cod` work; do not block #2 on v1.1 in advance.

### 2.3 Out of scope for #2

- Morphisms between bicomodules with different left or right bases (use the future `bicomodule_morphism_over` constructor).
- Tensor and parallel-product constructions on `BicomoduleMorphism` (additive follow-up).

### 2.4 Tests

- Identity morphism on a known bicomodule validates.
- A lens that fails the left-coherence square produces a `ValidationResult` with a localized failure.
- Composition of two morphisms validates iff each individual morphism validates.
- Worked example matching Niu/Spivak's bicomodule-morphism construction (whichever is closest in Ch. 8).

---

## 3. Kan extensions of bicomodules — two flavors, one PR

**Problem.** Sequence 3 (audit/likelihood arm) needs both Kan-extension constructions: (a) Kan extensions of comodules along a bicomodule, and (b) Kan extensions in the 2-category Cat#. Per Q3.1 resolution we ship both with distinct names. The audit confirmed nothing of either kind exists in v0.2.0.

### 3.1 Resolved design (2026-05-01)

**Two constructions, distinct names, single PR (split internally into 3a + 3b for review):**

```julia
# --- 3a: Kan extension of a comodule along a bicomodule (finite-only) ---

"""
    kan_along_bicomodule(D::Bicomodule, M::AbstractComodule; direction=:left) -> KanExtension

Given a bicomodule D : C ⇸ E (where C, E are comonoids = small categories)
and a comodule M of one side, return the Kan extension of M along D.

  - direction=:left  -> Σ_D : C-comodules -> E-comodules (left adjoint)
  - direction=:right -> Π_D : E-comodules -> C-comodules (right adjoint, dual shape)

Inputs must be finite (finite carriers, finite bases). Symbolic-aware
extension lives in `kan_2cat` (3b).
"""
kan_along_bicomodule(D::Bicomodule, M::AbstractComodule; direction=:left) :: KanExtension

# --- 3b: Kan extension in the 2-category Cat# (symbolic-aware) ---

"""
    kan_2cat(D::Bicomodule, F::Bicomodule; direction=:left) -> KanExtension

Kan extension in the 2-category obtained from Cat# by collapsing 2-cells.
Operates on bicomodules viewed as 1-cells. Accepts symbolic carriers and
bases — uses `LazySubst` and the symbolic layer where possible to avoid
forcing finite enumeration.

  - direction=:left  -> Lan_D F
  - direction=:right -> Ran_D F
"""
kan_2cat(D::Bicomodule, F::Bicomodule; direction=:left) :: KanExtension
```

**The `KanExtension` record** (Q3.3 resolution — richest option):

```julia
"""
    KanExtension{T}

Records the result of a Kan extension. Carries:
  - `extension::T`           the resulting comodule (3a) or bicomodule (3b)
  - `unit::BicomoduleMorphism`   the canonical 2-cell witnessing the
                                 universal property (counit when right Kan)
  - `factor_through(other)`  method exhibiting the universal property:
                             given any other 2-cell with appropriate shape,
                             returns the unique factorizing morphism
"""
struct KanExtension{T}
    extension::T
    unit::BicomoduleMorphism      # for left Kan; counit for right Kan
    # internal data needed by factor_through
end

factor_through(k::KanExtension, α::BicomoduleMorphism) :: BicomoduleMorphism
```

**Unicode aliases (Q3.4):** `Σ_D(M) = kan_along_bicomodule(D, M; direction=:left)` etc., exported alongside the prose names.

### 3.2 Resolutions (2026-05-01)

- **Q3.1 — Both constructions, distinct names.** `kan_along_bicomodule` (comodule-along-bicomodule) and `kan_2cat` (in the 2-category Cat#) are different operations and both ship.
- **Q3.2 — Split: finite for `kan_along_bicomodule`, symbolic-aware for `kan_2cat`.** 3a requires finite carriers and bases (matching how Sequence 3 is shaped today). 3b uses `LazySubst` and the symbolic layer to admit infinite (co)limits where the symbolic layer can express them. This split lets 3a land first if 3b's symbolic interactions surface unexpected blockers.
- **Q3.3 — Richer `KanExtension` record with universal-property witness.** Returns a struct carrying `extension`, `unit`/`counit` morphism, and a `factor_through` method that exhibits the universal property. Without this, downstream audit/likelihood reasoning that depends on the universal property has to reconstruct it from the extension object alone.
- **Q3.4 — Both names exported.** `kan_along_bicomodule` / `kan_2cat` for prose; `Σ_D` / `Π_D` as unicode aliases. Matches existing `⊗`/`▷`/`⊙` house style.

### 3.3 Companion design note

`docs/dev/kan_extensions_construction.md` accompanies the PR, pinning down the categorical construction with specific Niu/Spivak Ch. 8 references for both 3a and 3b. Likely 3–5 pages; written before implementation begins.

### 3.4 Tests

- Identity bicomodule: `kan_along_bicomodule(id_bicomod, M)` equals `M`.
- Identity bicomodule: `kan_2cat(id_bicomod, F)` equals `F`.
- Universal property: `factor_through(k, k.unit)` is the identity.
- Universal property: for any compatible `α`, `factor_through(k, α)` composed back through `k.unit` recovers `α`.
- Audit/likelihood worked example (reviewer-supplied) whose output is computable by hand.

---

## 4. `support(X, φ)` — Set-sets / minimal-dependency operator

**Problem.** Sequence 4 (explainability) needs `support(X, φ)` — given a polynomial functor `X` and an element `φ ∈ X(S)`, return the minimal subset of `S` that `φ` actually depends on. This generalizes "free variables of an expression" to arbitrary polynomial structures. The audit confirmed: nothing like this exists in v0.2.0.

The construction (Fairbanks, Topos blog) is sometimes called the "Set-sets" construction. The key fact: for `X = Σ_{i∈I} y^{X[i]}`, an element `φ ∈ X(S)` is a pair `(i, f : X[i] → S)`, and `support(X, φ) = image(f) ⊆ S`.

### 4.1 Proposed design

```julia
"""
    support(p::Polynomial, position, assignment::PolyFunction) -> PolySet

Minimal subset of the codomain that `(position, assignment)` depends on,
viewing the pair as an element of `p(S)` where `S` is the codomain
of `assignment`.

For p = Σᵢ y^{p[i]}, support is the image of `assignment` viewed as a
function p[position] → S.
"""
support(p::Polynomial, position, assignment::PolyFunction) :: PolySet

# Convenience signature where the user has already built the X(S) element:
support(elem::PolyElement) :: PolySet     # if we add a PolyElement wrapper
```

Beyond the base case for `Polynomial`, support generalizes:

- **`Comonoid`** — support of a state under the duplicator is the set of "next" states reachable; this may already be derivable but expose it for users.
- **`Bicomodule`** — support relative to a coaction; what does an element depend on through the left (or right) coaction?
- **Symbolic** — support of a `SymbolicPolynomial` element mirrors free-variable computation and could be the most useful version.

### 4.2 Resolutions (2026-05-01)

- **Q4.1 — Introduce `PolyElement` wrapper.** `PolyElement(p, position, assignment)` becomes the canonical handle for "an element of p(S)". `support(::PolyElement)` is the primary method; `support(p, position, assignment)` forwards. Sets up the type system for downstream extensions (Bicomodule, Comonoid, Symbolic versions of support all reuse this handle in subsequent PRs).
- **Q4.2 — Just `Polynomial` in #4.** Bicomodule and Comonoid generalizations of support deferred to follow-up PRs. Get the base case solid first.
- **Q4.3 — Include symbolic in #4.** Symbolic support ships alongside concrete in the same PR. This means free-variable analysis of `SymExpr` trees lands as part of #4. Bigger PR but no API drift between concrete and symbolic later. Pushes #4 from M to **L**.
- **Q4.4 — Fairbanks-style support, with f∘u=g∘u semantics.** `support(p, φ)` returns the minimal `U ⊆ S` such that for all `f, g : S → T` with `f|_U = g|_U`, we have `f·φ = g·φ`. For polynomial functors specifically this coincides with strong support and equals `image(assignment)`. Documented relationship to strong support so the API stays right when Set-sets-with-equations are added later.

### 4.3 Out of scope for #4

- Support on `Bicomodule` and `Comonoid` carriers (follow-up PRs).
- Reverse direction: given a subset `S' ⊆ S`, return all `φ ∈ X(S)` with `support(X, φ) ⊆ S'`.

### 4.4 Tests

- Constant polynomial: support is empty.
- Linear polynomial `Sy`: support is the singleton image.
- Monomial `y^k`: support is image of the `k`-tuple.
- Reviewer-provided Sequence 4 case: a known explainability scenario whose support has been computed by hand.

---

## 5. `bicomodule_from_data` constructor

**Problem.** The reviewer hand-rolled a constructor in `ProtocolCompileV2.jl` that builds a `Bicomodule` from data tables (carrier, base comonoids, and three Dicts: `f_table`, `emit_table`, `sharp_L_table`). The generic version belongs in Poly.jl. Without it, every downstream user reinvents the dependent-function bookkeeping.

### 5.1 Proposed design

```julia
"""
    bicomodule_from_data(
        carrier::Polynomial,
        left_base::Comonoid,
        right_base::Comonoid;
        left_position_map::Dict,           # carrier_pos -> left_base_pos
        right_position_map::Dict,          # carrier_pos -> right_base_pos
        left_back_directions::Dict,        # (carrier_pos, left_dir_at_image) -> carrier_dir
        right_back_directions::Dict,       # (carrier_pos, carrier_dir) -> right_dir_at_image
    ) -> Bicomodule

Build a Bicomodule from authored data tables. Constructs the two coaction
Lens objects internally, validates the result via
validate_bicomodule_detailed, and returns the Bicomodule (or throws with
the failures).
"""
bicomodule_from_data(carrier, left_base, right_base; ...) :: Bicomodule
```

The constructor:
1. Builds a `PolyFunction` for each position map from the supplied `Dict`.
2. Builds a `DependentFunction` for each back-direction table from the supplied `Dict`.
3. Wraps them as two `Lens` objects with appropriate `cod` (using `subst_lazy` to avoid eager enumeration).
4. Constructs the `Bicomodule`.
5. Calls `validate_bicomodule_detailed` and throws `ArgumentError` with a `minimal_failing_triple` summary on failure.

### 5.2 Resolutions (2026-05-01)

- **Q5.1 — Descriptive keyword names.** `left_position_map`, `right_position_map`, `left_back_directions`, `right_back_directions`. Self-documenting; the constructor is rare-call so verbosity isn't a cost.
- **Q5.2 — Yes, `validate=false` escape hatch.** Default validates (catches authoring mistakes loudly); users opt out for intermediate bicomodules they know are invalid in isolation but valid in combination.
- **Q5.3 — Bundle `comonoid_from_data` in this PR.** Symmetric construction: `comonoid_from_data(carrier; eraser_table::Dict, duplicator_position_map::Dict, duplicator_back_directions::Dict)`. Mirrors the bicomodule API and saves a future round-trip. Adds modestly to PR size but stays at M.

### 5.3 Out of scope for #5

- A symbolic version. Authored-tables imply finite, concrete data.

### 5.4 Tests

- Round-trip: build a bicomodule via the existing constructor, extract the position maps and back-direction tables, rebuild via `bicomodule_from_data`, check structural equality.
- Reviewer's `ProtocolCompileV2.jl` use-case rewritten to call this.
- Validation failure produces a localized `minimal_failing_triple` error message.

---

## 6. `sharp_L` / `sharp_R` as inspectable, finite-materializable accessors

**Problem.** The back-direction map of a `Lens` lives inside `Lens.on_directions::DependentFunction` (`Lens.jl:32`). It is callable but opaque — you cannot easily enumerate, pretty-print, or dump it for debugging. For `Bicomodule`, the user needs to inspect the back-directions of both coactions (informally `sharp_L` and `sharp_R`), and currently has to reach into `.on_directions.f` (internal).

**Audit clarification:** `sharp_L` / `sharp_R` are **not** existing names in the codebase. The reviewer is using these as proposed names for "the back-direction map of the left (resp. right) coaction." They will be introduced by this PR.

### 6.1 Proposed design

Two layers:

**Layer A — generic Lens accessor:**

```julia
"""
    back_directions(L::Lens; materialize=:auto) -> Union{Function, Dict}

Expose the back-direction map of a Lens. Returns either:
  - a callable (the underlying `on_directions.f`) when `L.dom` has
    infinite or large positions and `materialize=:auto`, or when
    `materialize=false`;
  - a Dict mapping (position, cod_direction) -> dom_direction when
    finite-and-small, or when `materialize=true`.

The `:auto` cutoff is `TABULATE_SIZE_CAP` (shared with subst tabulation).
"""
back_directions(L::Lens; materialize=:auto) :: Union{Function, Dict}
```

**Layer B — Bicomodule-specific shorthands:**

```julia
sharp_L(B::Bicomodule; materialize=:auto)  =  back_directions(B.left_coaction;  materialize=materialize)
sharp_R(B::Bicomodule; materialize=:auto)  =  back_directions(B.right_coaction; materialize=materialize)
```

### 6.2 Resolutions (2026-05-01)

- **Q6.1 — Custom `BackDirectionTable` struct with pretty `show`.** Returns a struct (not a raw `Dict`) that wraps the back-direction map and provides a REPL-friendly `show` method printing by position with indentation. Accessors: `pairs(::BackDirectionTable)`, `getindex(::BackDirectionTable, position, cod_dir)`, iteration. This is a step up in API surface from the recommendation but pays off when users are debugging non-trivial bicomodules and want pretty output by default.
- **Q6.2 — Error if `materialize=true`, fall back to callable if `:auto`.** Explicit user request over the cap errors with the cap-message style from Extensions v1 #7. `:auto` (default) silently returns the callable form. Predictable; consistent with existing house style.

### 6.3 Out of scope for #6

- Forward `on_positions` accessor — already trivially `L.on_positions`, no wrapper needed.
- Modifying `Lens` internals.

### 6.4 Tests

- Finite small `Lens`: `back_directions` returns a `Dict` matching hand-computed ground truth.
- Finite large `Lens` with `materialize=:auto`: returns callable, doesn't enumerate.
- `materialize=true` on too-large Lens: errors with cap message.
- `sharp_L(B)` and `sharp_R(B)` return the per-coaction maps for a worked-example bicomodule.

---

## 7. `minimal_failing_triple` worked-example docstring

**Problem.** `minimal_failing_triple` is exported (`Validation.jl:132`, audit-confirmed) and has a docstring, but the docstring doesn't show how to chain it after `validate_bicomodule_detailed` to localize a failure. The reviewer wants a concrete example.

### 7.1 Proposed design

Update the existing docstring to include a worked example: build an intentionally-invalid bicomodule (e.g., flip one back-direction), run `validate_bicomodule_detailed`, pass `result.failures` to `minimal_failing_triple`, interpret the returned triple. ≤ 30 lines of example code.

### 7.2 Open questions

None.

### 7.3 Tests

- Doctest the example so it stays current.

---

## 8. Lazy `cofree_comonoid` variant

**Problem.** `cofree_comonoid(p, depth)` is eager (`Cofree.jl:188–215`, audit-confirmed): it enumerates all behavior trees of depth ≤ d up front. The combinatorial caveat in the file header ("d ∈ {1, 2, 3} with small p") bites quickly — e.g., `Σ_obs_v2` with 8 elements at depth 5 is ~37k directions per tree.

The reviewer wants a lazy variant materializing trees and paths on demand, modeled on `subst_lazy` / `materialize` (`Monoidal.jl:786–793`).

### 8.1 Proposed design

```julia
"""
    LazyCofreeComonoid(p::Polynomial, depth::Int) <: AbstractComonoid

Cofree comonoid on `p` up to depth `d`, with trees and paths
materialized only when queried. Mirrors the LazySubst pattern:
shape-level operations (eraser, identity, structural equality of
neighbouring lazy cofrees) work without enumeration.

Materializes only when:
  - `materialize(::LazyCofreeComonoid) -> Comonoid` is called explicitly;
  - a query forces enumeration (e.g., asking for the full set of trees).

Most categorical operations (composing with a lens, applying
parallel/▷, pulling back coactions) work on the lazy form.
"""
struct LazyCofreeComonoid <: AbstractComonoid
    p::Polynomial
    depth::Int
end

cofree_lazy(p::Polynomial, depth::Int) :: LazyCofreeComonoid
materialize(c::LazyCofreeComonoid)     :: Comonoid
```

This introduces `AbstractComonoid` (mirroring the `AbstractPolynomial` move from Extensions v1 #1), with `Comonoid` aliased to `ConcreteComonoid` internally and `LazyCofreeComonoid` as a peer.

### 8.2 Resolutions (2026-05-01)

- **Q8.1 — All four operations work on the lazy form** (multi-select, all selected): `eraser` access, shape-level `validate_comonoid`, structural equality between two lazy cofrees with same `(p, depth)`, and `parallel(::LazyCofreeComonoid, ::LazyCofreeComonoid)`. The stretch goal is in scope; lazy carrier-tensor of two lazy cofrees never forces full enumeration. This makes #8 substantially more useful for downstream applications composing per-disease lazy cofrees.
- **Q8.2 — Yes, `tree_at(c, index)`.** Mirrors `direction_at` on `LazySubst`. Lets users query one tree out of an astronomical set without enumerating all of them.
- **Q8.3 — Cache materialized trees with a documented `clear_cache!` method.** Standard Julia idiom; repeated tree access in the same session is fast; users can free memory explicitly when needed.

### 8.3 Out of scope for #8

- Lazy versions of `RightComodule`, `LeftComodule`, `Bicomodule` carriers built over lazy cofrees. Likely follow-up if downstream needs them.

### 8.4 Tests

- Building `cofree_lazy(p, 3)` for a polynomial that would OOM the eager version: completes instantly.
- `materialize(cofree_lazy(p, 2)) == cofree_comonoid(p, 2)` for small `p`.
- Eraser / validate / parallel work on lazy form without triggering full enumeration (assert via a counter on `_trees_at_depth`).

---

## 9. `validate_bicomodule_detailed` — explicit axiom listing

**Problem.** The docstring describes the function's purpose but doesn't enumerate the five coherence axioms it checks. From audit (`Cofree.jl:1262–1373`): counit-L, counit-R, coassoc-L, coassoc-R, compatibility (with positions and directions sub-checks). Users interpreting failures benefit from a clear axiom list.

### 9.1 Proposed design

Update the docstring to enumerate the axioms and link each to where the failure surfaces in `ValidationResult.failures`. Add an "Interpretation" section showing the naming convention used in failure messages.

### 9.2 Open questions

None.

### 9.3 Tests

- Doctest the axiom-list example.

---

## 10. Cofree depth tradeoff — formula + table in `Cofree.jl` header

**Problem.** The current header (`Cofree.jl:21–23`, audit-confirmed) says only "Useful for d ∈ {1, 2, 3} with small p; demos and tests stay in that range." The reviewer wants a concrete formula or table so users can predict cost at a chosen depth.

### 10.1 Proposed design

Replace the prose caveat with a formula + small table. For `p = y^n` (single position, n directions), the count of behavior trees at depth `d` follows the recurrence `T(d) = n^{T(d-1) · n}` with `T(0) = 1`. For general `p` with positions of varying arity, the recurrence sums over positions. Document both.

Add a table for small `n` and `d ≤ 4`:

```
n \ d   0    1    2         3                    4
---------------------------------------------------------
1       1    1    1         1                    1
2       1    4    256       ~1.16 × 10^77        astronomical
3       1    27   ~10^14    ~astronomical        ...
```

(Exact values to be filled in during implementation.)

### 10.2 Resolutions (2026-05-01)

- **Q10.1 — Verify numerically.** Run `_trees_at_depth(p, d)` for `n ∈ {2, 3}` and `d ∈ {1, 2, 3}`; assert the proposed recurrence matches. Add a doctest in the docs page so the formula stays correct if the underlying enumeration ever changes.

### 10.3 Tests

Doctest the formula table against numerically-derived ground truth.

---

## 11. Worked-example bicomodule walkthrough doc

**Problem.** Niu/Spivak presents bicomodule examples in Ch. 8 but reading them and translating to Julia is its own task. A walkthrough document on the Julia side — taking a specific Niu/Spivak example, building it step by step using `bicomodule_from_data` (#5), validating with `minimal_failing_triple` (#7), inspecting with `sharp_L` / `sharp_R` (#6) — is the missing onboarding piece for someone building a bicomodule from scratch.

### 11.1 Proposed design

A new `docs/src/examples/bicomodule_walkthrough.md`, structured as:

1. The mathematical setup: which Niu/Spivak example, what the carrier and base comonoids are.
2. Building each `Comonoid` from data.
3. Building the `Bicomodule` via `bicomodule_from_data`.
4. Validating: `validate_bicomodule_detailed`, interpreting any failures via `minimal_failing_triple`.
5. Inspecting: pretty-print `sharp_L` / `sharp_R`.
6. Modules-of-it: build a `LeftComodule` and `RightComodule` over the bicomodule.

### 11.2 Resolutions (2026-05-01)

- **Q11.1 — Library author selects.** Pick a clean Ch. 8 example for the walkthrough — likely the prafunctor example or a small Kleisli-flavored bicomodule. Reviewer sanity-checks at PR review.

### 11.3 Depends on

- #1 (parallel comonoid), #5 (`bicomodule_from_data`), #6 (`sharp_L` / `sharp_R`). Land last in v0.3.

### 11.4 Tests

- Doctest the walkthrough end-to-end.

---

## 12. `representable(::Vector)` overload

**Problem.** `representable(A::PolySet)` (`Polynomial.jl:96–97`) requires a `PolySet` (typically `FinPolySet`). One less wrapping step would shave a line in tutorials and examples.

### 12.1 Proposed design

```julia
representable(v::AbstractVector) = representable(FinPolySet(v))
representable(s::AbstractSet)    = representable(FinPolySet(collect(s)))
```

### 12.2 Tests

- `representable([:a, :b, :c]) == representable(FinPolySet([:a, :b, :c]))`.

---

## 13. `cofree_comonoid(::Comonoid, depth)` — DEFERRED to Extensions v3

**Status (2026-05-01):** Per Q13.1 resolution, deferred to a future Extensions v3 round. The universal property of "cofree on a comonoid" is fuzzy enough that doing it half-right in v0.3 would be worse than skipping; park as a research item.

When this is picked up, the placeholder design lives in this section's git history. A companion note `docs/dev/cofree_over_comonoid.md` should be written before any implementation begins, pinning down the universal property and computability story.

---

## 14. `free_category_comonoid(vertices, edges)` constructor

**Problem.** `from_category(::SmallCategory)` (`Comonoid.jl:201`, audit-confirmed) takes a built `SmallCategory`. Building the free category on a graph by hand is rote. Reviewer ended up reaching for `from_category` after manually constructing the `SmallCategory` for `P_d` — would have preferred to skip that step.

### 14.1 Proposed design

```julia
"""
    free_category_comonoid(vertices::AbstractVector, edges::AbstractVector{Tuple}) -> Comonoid

The comonoid corresponding to the free category on the directed graph
with the given vertices and edges. Edges are (source, target) tuples;
identity morphisms and composites are added automatically.
"""
free_category_comonoid(vertices, edges) :: Comonoid
```

Internally: build the free `SmallCategory` (paths in the graph as morphisms, concatenation as composition, vertices as objects), then call `from_category`.

### 14.2 Resolutions (2026-05-01)

- **Q14.1 — Multi-arity dispatch on tuple shape.** Accept both `(src, tgt)` and `(src, tgt, label)` forms in the same `edges` argument. Bare tuples auto-generate labels by position; labeled tuples use the user-supplied label as the morphism name.
- **Q14.2 — Depth-bounded with a clear warning.** When the input graph contains cycles, the constructor returns a depth-bounded free category (paths up to a `max_depth` keyword, default e.g. 3) and emits an `@warn` explaining that cycles were detected and the bound is being applied. Categorically this is a finite truncation of the infinite free category. Documented limitation: the resulting comonoid is *not* the actual free comonoid for cyclic inputs; users wanting the full lazy infinite version need to wait for the lazy-cofree infrastructure from #8 to extend to free categories.

### 14.3 Tests

- Free category on a one-edge graph: agrees with hand-built `from_category` result.
- Free category on a tree: each path is a distinct morphism.
- Free category on a cyclic graph with `max_depth=2`: returns a comonoid whose morphisms are paths of length ≤ 2, emits a warning.
- Mixed labeled/unlabeled edges: both work in the same call.

---

## 15. `@poly` macro — examples surfaced in docs

**Problem.** `@poly` (`Macros.jl:66–159`, audit-confirmed) is exported but the audit notes it's "not heavily used in the core library itself, primarily a user-facing convenience." Surfacing usage examples in docs would tell users it exists.

### 15.1 Proposed design

Add a section to `docs/src/getting_started.md` (or wherever introductory material lives) showing `@poly` syntax for the common construction patterns:

- `@poly y` (representable on singleton)
- `@poly y^k` (monomial)
- `@poly 2y` (sum of representables)
- `@poly y^2 + 3y + 1` (full polynomial expression)
- `@poly y^a ⊗ y^b` (tensor)
- `@poly y^a ▷ y^b` (substitution)

Cross-reference from the `Polynomial` docstring.

### 15.2 Open questions

None.

### 15.3 Tests

- Doctest the examples section so the macro stays in sync with what the docs claim.

---

## 16. Dependency graph & PR ordering

```
Tier 0 (mechanical, parallel-landable):
  #12 (representable Vector)   ─┐
  #7  (minimal_failing_triple)  │
  #9  (validate axioms doc)     │  no inter-deps
  #10 (cofree depth formula)    │
  #14 (free_category_comonoid)  │
  #15 (@poly macro examples)   ─┘

Tier 1 (Sequence 1 unblock):
  #1  (parallel comonoid + ⊗ deprecation; validates at construction)

Tier 2 (Sequence 2 unblock):
  #6  (back_directions + BackDirectionTable + sharp_L/sharp_R)
       ──>  #5  (bicomodule_from_data + comonoid_from_data)
            ──>  #2  (BicomoduleMorphism with full horizontal composition)

Tier 3 (Sequence 3 unblock):
  #3  (Kan extensions: 3a kan_along_bicomodule finite + 3b kan_2cat symbolic;
       both share KanExtension record)  [depends on #2]

Tier 4 (Sequence 4 unblock):
  #4  (support: concrete + symbolic, with PolyElement wrapper)
       [independent of #2/#3]

Tier 5:
  #8  (lazy cofree with full lazy-comonoid algebra)
  #11 (worked-example bicomodule doc)  [depends on #1, #2, #5]

Deferred to Extensions v3:
  #13 (cofree_comonoid over a base comonoid)
```

**Release plan (per Q-resolution 2026-05-01):** single **v0.3.0** bundling everything above. Reviewer chose this over the split-release option to ship one coherent extension round. Internal review-time split: #3 may be reviewed as 3a + 3b PRs but lands in the same release tag. #11 and #8 land near the end of the release window.

---

## 17. Resolutions log (2026-05-01)

All open questions resolved in a structured Q&A pass with the reviewer. Decisions below; off-recommendation choices flagged for traceability.

| ID | Question | Resolution |
|---|---|---|
| Q1.1 | `⊗(::Comonoid, ::Comonoid)` semantics shift | **Hard break in v0.3** (revised from soft 2026-05-01 — `⊗` ≡ `parallel` via `const var"⊗" = parallel`, so they cannot disagree by signature) |
| Q1.2 | `parallel(::Comonoid, ::Comonoid)` validate at construction? | **Yes, validate** (off-recommendation; user prefers belt-and-suspenders) |
| Q2.1 | BicomoduleMorphism: bases by `===` or `==`? | **`===`** (object identity) |
| Q2.2 | Horizontal composition in scope for #2? | **Yes, include in #2** (off-recommendation; #2 grows L → XL, full double-category 2-cells) |
| Q2.3 | `validate_bicomodule_morphism_detailed` returns `ValidationResult`? | **Yes**, mirror exactly |
| Q2.4 | Coherence under lazy `Lens.cod` — depend on v1.1? | **Lazy-first, fall back as needed** |
| Q3.1 | Which Kan-extension construction? | **Both** — `kan_along_bicomodule` + `kan_2cat`, distinct names |
| Q3.2 | Computability constraints | **Split: finite for `kan_along_bicomodule`, symbolic-aware for `kan_2cat`** (off-recommendation; biggest scope option) |
| Q3.3 | Return universal cocone/cone or just object? | **Richer `KanExtension` record** with universal-property witness `factor_through` (off-recommendation; richest option) |
| Q3.4 | Export `Σ_D` / `Π_D` unicode names? | **Both prose and unicode names** exported |
| Q4.1 | `PolyElement` wrapper? | **Yes**, introduce wrapper |
| Q4.2 | Support on `Bicomodule`/`Comonoid` in #4? | **Just `Polynomial`** in #4 |
| Q4.3 | Symbolic support — separate PR? | **Include in #4** (off-recommendation; #4 grows M → L) |
| Q4.4 | Fairbanks construction exact form? | **Fairbanks-style support** (f∘u=g∘u semantics); for polynomials this equals image(assignment); document distinction from strong support |
| Q5.1 | `bicomodule_from_data` keyword names | **Descriptive** (`left_position_map` etc.) |
| Q5.2 | `validate=false` escape hatch? | **Yes**, opt-in skip |
| Q5.3 | Bundle `comonoid_from_data`? | **Yes, bundle** (off-recommendation; symmetric construction shipping together) |
| Q6.1 | `back_directions` return type? | **Custom `BackDirectionTable` struct** with pretty `show` (off-recommendation; better DX, slightly more API) |
| Q6.2 | Cap-exceeded behavior? | **Error if `materialize=true`, fallback if `:auto`** |
| Q8.1 | Which Comonoid ops work on lazy form? | **All four**: eraser, validate, equality, AND `parallel` (off-recommendation; max scope including stretch goal) |
| Q8.2 | `tree_at(c, index)` for single-tree materialization? | **Yes**, mirror `direction_at` on `LazySubst` |
| Q8.3 | Cache materialized trees? | **Yes**, with `clear_cache!` method |
| Q10.1 | Cofree formula — verify numerically? | **Yes**, derive against `_trees_at_depth` and assert match |
| Q11.1 | Which Niu/Spivak example for the walkthrough? | **Library author selects** (clean Ch. 8 example, reviewer sanity-checks at PR review) |
| Q13.1 | Cofree-on-a-comonoid universal property? | **Defer #13 to Extensions v3** |
| Q13.2 / Q13.3 | (subordinate to Q13.1) | Closed by Q13.1 deferral |
| Q14.1 | Edge labels supported? | **Yes**, multi-arity dispatch on tuple shape |
| Q14.2 | Cyclic graphs — refuse or lazy? | **Depth-bounded with `@warn`** (custom hybrid: takes `max_depth` keyword, emits warning when cycles detected, returns finite truncation) |

**Off-recommendation tally:** Q1.2, Q2.2, Q3.2, Q3.3, Q4.3, Q5.3, Q6.1, Q8.1, Q14.2. Cumulative effect: #2, #3, #4, #5, #6, #8, #14 all grew compared to the original draft. Release scope expanded but kept as a single v0.3.0 per reviewer's release-plan choice.

**Release plan resolution:** **single v0.3.0** bundling everything (off-recommendation; reviewer chose this over a v0.3.0/v0.3.1 split to ship one coherent extension round).
