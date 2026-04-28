# Poly.jl — Extensions v1 Design Doc

> **Status**: design-only. No code lands until this is signed off. Each numbered item maps to a separate PR.
>
> Drafted from a structured review of an external user who built a non-trivial application on Sprint 8 Poly.jl. Nine items, ranked by what changes *what is expressible* vs. what changes *how comfortable it is*. Reviewer commentary preserved verbatim where it was load-bearing.

---

## 0. Summary

| # | Item | Class | Breaks API? | PR size | Depends on |
|---|---|---|---|---|---|
| 1 | Lazy / shape-only `subst` equality | Expressivity | No (additive) | M | — |
| 2 | Monoidal operators on `Comonoid` and `Bicomodule` | Expressivity | No (additive) | L | #1 |
| 3 | n-ary flat `coproduct` | Ergonomics | No (additive) | S | — |
| 4 | First-class `Coalgebra` peer type | Expressivity | No (additive) | M | — |
| 5 | `subst_targeted_lens` helper | Ergonomics | No (additive) | S | #1 (uses lazy form) |
| 6 | Structural validation diagnostics | Ergonomics | Soft (return type) | M | — |
| 7 | `TABULATE_SIZE_CAP` error message | Ergonomics | No | XS | — |
| 8 | Symbolic ↔ concrete interop polish | Ergonomics | No (additive) | S | — |
| 9 | Examples coverage (Bicomodule, retrofunctor, cofree) | Coverage | No | M | #1, #2, #4 |

**Phasing:** three PRs of foundations (#1, #4, #6), three PRs of operators and helpers (#2, #3, #5), three PRs of polish (#7, #8, #9). One PR per item. See §11 for the dependency graph.

**Where the codebase stands today.** Concrete layer is feature-complete through Sprint 8 (Niu/Spivak Ch. 1–8). `Symbolic.jl` exists but is shallow — expression trees, `lift`, `evaluate`, basic simplification — and never participates in `Bicomodule` construction or `subst` equality. The reviewer's findings are all gaps between "we built the symbolic layer" and "the symbolic layer is reachable from the places that matter."

---

## 1. Lazy / shape-only `subst` equality

**Problem.** `subst(p, q)` (`Monoidal.jl:203–259`) eagerly enumerates `|q.positions|^|p.directions(i)|` j̄-functions per position of `p`, stored as tuples of `Dict`s. Bicomodule construction (`Cofree.jl:705,709`) type-checks via

```julia
left_coaction.cod == subst(left_base.carrier, carrier) ||
    error("Bicomodule: left_coaction.cod ≠ left_base.carrier ▷ carrier")
```

`==` on `Polynomial` (`Polynomial.jl:110–117`) is structural and forces materialization of every direction-set. So *constructing any bicomodule* enumerates the substitution polynomial in full. Reviewer hit this at S with 5-direction objects and A with 16 positions — already in the millions.

**Why the existing symbolic layer doesn't help.** `Symbolic.jl` builds `SymExpr` trees but never feeds back into `Polynomial`'s equality or `Bicomodule`'s constructor. The lazy machinery exists; it just isn't reachable from the path that matters.

### 1.1 Proposed design — three layers, smallest-first

**Layer A (the unblocker, lands first):** a structural equality predicate that recognizes "this polynomial *is* the substitution of those two" without enumerating j̄-functions.

```julia
"""
    is_subst_of(target::Polynomial, p::Polynomial, q::Polynomial) -> Bool

True iff `target` is structurally equal to `subst(p, q)` *as a polynomial*,
deciding the question without enumerating j̄-functions where possible.

Decision procedure (cheapest first):
  1. If `target` is a `LazySubst(p′, q′)` and `(p′, q′) ≡ (p, q)`, return true.
  2. If `target.positions` is finite and `|target.positions| ≠ Σᵢ |q(1)|^|p[i]|`,
     return false. (O(|p(1)|) without touching directions.)
  3. Sample-check: pick one position from each side and verify the (i, j̄)
     unpacking matches and direction-set sizes line up. Cheap sanity gate.
  4. Fall back to full structural `==` only if the user explicitly opts in
     via `force_enumerate = true` or `target` has been materialized already.
```

`Bicomodule`'s constructor switches from `==` to `is_subst_of`:

```julia
is_subst_of(left_coaction.cod, left_base.carrier, carrier) ||
    error("Bicomodule: left_coaction.cod ≠ left_base.carrier ▷ carrier")
```

**This single change is the unblocker.** It is small, additive, and gives the reviewer's class of bicomodules buildable.

**Layer B (deferred construction):** a `LazySubst` polynomial that *acts* like the result of `subst(p, q)` but defers j̄ enumeration until something asks for a position.

```julia
struct LazySubst <: AbstractPolynomial    # see §1.2 for the supertype
    p::Polynomial
    q::Polynomial
end

# Interface methods that don't enumerate:
positions_cardinality(s::LazySubst)        # Σᵢ |q(1)|^|p[i]|, returns Cardinality
direction_at(s::LazySubst, pos)            # decodes pos = (i, j̄), returns Σ_a q[j̄(a)]
materialize(s::LazySubst) -> Polynomial    # expensive; only on explicit request
```

`subst_lazy(p, q) -> LazySubst` is the lazy constructor. Existing `subst(p, q) -> Polynomial` is preserved (eager) for callers that want concrete output.

**Layer C (composition):** because `LazySubst` is itself a polynomial, `subst_lazy(LazySubst(p, q), r) -> LazySubst` works without ever materializing. This is what unblocks composing bicomodules over composition products.

### 1.2 The supertype — resolved

**Decision (Q1, 2026-04-28):** introduce `abstract type AbstractPolynomial end` and reseat `Polynomial` underneath it. The current concrete struct is renamed `ConcretePolynomial` internally; the public name `Polynomial` is preserved via `const Polynomial = ConcretePolynomial`. `LazySubst <: AbstractPolynomial` is the second peer.

Method signatures typed `::Polynomial` continue to work via the alias for *callers*. Internal methods that need to dispatch on both kinds use `::AbstractPolynomial`. Methods that genuinely require the concrete representation (e.g., `==` on materialized positions) keep the `::ConcretePolynomial` type.

Migration impact for users: zero, unless they pattern-match on Julia's nominal type — which `from_category` etc. don't.

### 1.3 Out of scope for #1

- Lazy product, lazy coproduct, lazy ⊗. These are easier (no exponential blow-up) and we don't need them yet. Add when motivated.
- Symbolic *infinite* polynomials (the `SymbolicPolynomial` path). Layer C above is enough for the substitution-explosion case; full infinite-set support is a separate effort and tracked in `project_poly_julia_todo.md`.

### 1.4 Tests

- Reviewer's pathological case: `S = Sy^S` for `|S| = 5` and `A` polynomial with 16 positions, each with up to 5 directions. `Bicomodule` construction should complete in milliseconds.
- `is_subst_of` returns false fast when cardinalities mismatch (no enumeration triggered).
- Round-trip: `materialize(subst_lazy(p, q)) == subst(p, q)` for finite cases.

---

## 2. Monoidal operators on `Comonoid` and `Bicomodule`

**Problem.** `Polynomial` and `Lens` have `+`, `×` (`*` in Julia), `⊗`, `▷`. None of these lift to `Comonoid` or `Bicomodule`. To form `c + d` as a `Comonoid` users must build the eraser and duplicator over the combined carrier by hand and route tagged positions through `▷`. For bicomodules, `M ⊗ N`, `M + N`, `M ⊙_D N` are all natural categorical operations and none are exposed.

### 2.1 Proposed design — the operator surface

**On `Comonoid`** (= a small category, by Ahman–Uustalu):

```julia
Base.:+(c::Comonoid, d::Comonoid)       :: Comonoid    # disjoint union of categories
Base.:*(c::Comonoid, d::Comonoid)       :: Comonoid    # product of categories
⊗(c::Comonoid, d::Comonoid)             :: Comonoid    # parallel (Dirichlet) — see §2.3
```

Semantics — derived from the underlying small categories, then transported back through `from_category`:

| Operator | Objects | Morphisms | Identity | Composition |
|---|---|---|---|---|
| `c + d` | `Ob(c) ⊔ Ob(d)` | `Mor(c) ⊔ Mor(d)` | side-tagged | within-side |
| `c * d` | `Ob(c) × Ob(d)` | pairs of morphisms | pair of identities | componentwise |
| `c ⊗ d` | `Ob(c) × Ob(d)` | `Mor(c) × Mor(d)` (parallel) | pair of identities | componentwise |

`*` and `⊗` agree on small categories — but that's a coincidence of `Cat`, not a coincidence in `Cat#`. Worth being explicit: `c * d` is the categorical product (limit), `c ⊗ d` is the parallel product inherited from `Polynomial ⊗`. In `Cat` they coincide; we expose both for symmetry with `Polynomial`.

**Implementation strategy:** for `+` and `*`, build the eraser/duplicator directly on the combined polynomial carriers using the existing `Polynomial`-level `+` and `*`. For `⊗`, derive via `to_category → product → from_category` (slower but unambiguous). Document the equivalence in tests.

**On `Bicomodule`**:

```julia
Base.:+(M::Bicomodule, N::Bicomodule)             :: Bicomodule    # sum (requires same bases)
⊗(M::Bicomodule, N::Bicomodule)                   :: Bicomodule    # parallel (bases tensor)
compose(M::Bicomodule, N::Bicomodule)             :: Bicomodule    # M ⊙_D N when M.right_base == N.left_base
```

`compose` is the prafunctor composition (Niu/Spivak Ch. 8): given `M : C ↛ D` and `N : D ↛ E`, build `M ⊙_D N : C ↛ E`. Carrier is built from a coequalizer over `D`'s coactions; there's machinery for this in the book that the implementation needs to follow precisely. **This is the largest single piece of new math in the package** and warrants its own subsection during implementation. For the design doc, the API surface is what's being committed to — the implementation will document the coequalizer construction in code.

### 2.2 Validation

Each operator returns a constructed object. Constructor type-checks shapes (same as today). New `validate_*_compose` functions check that the result satisfies comonoid / bicomodule laws — these are useful both as tests and as user-facing sanity checks.

### 2.3 The `⊗` ambiguity

`Polynomial ⊗` in this library is the Dirichlet product, transposing positions and directions. On `Comonoid`, what does `⊗` mean? Two candidates:

- **(a)** Tensor of the underlying polynomial structure; the result is a comonoid iff the operation lifts cleanly. By inspection, the duplicator and eraser do lift, so this works.
- **(b)** Tensor in `Cat#` — which corresponds to the Cartesian product of categories.

(a) and (b) coincide when the comonoids represent small categories (which they always do, by Ch. 7), so this is a non-issue in practice. Document that `c ⊗ d` and `c * d` are equal as comonoids and let users pick by intent.

### 2.4 Out of scope for #2

- `▷` (composition product) on `Comonoid` and `Bicomodule`. The categorical meaning of `c ▷ d` for comonoids is "the composite category" but the composition product itself is more naturally about polynomials, not comonoids. Skip until motivated.

### 2.5 Tests

- `c + d` and `c * d` validate as comonoids.
- `to_category(c + d) ≅ to_category(c) ⊔ to_category(d)`.
- `M ⊗ N` validates as a bicomodule.
- `compose(regular_bicomodule(c), regular_bicomodule(c))` round-trips through `regular_bicomodule(c)` (modulo isomorphism — exact equality via the coequalizer structure).

---

## 3. n-ary flat `coproduct`

**Problem.** `p_a + p_b + p_c` (left-associated) gives positions like `(1, (1, :a)), (1, (2, :b)), (2, :c)`. Reviewer wrote a `unwrap_obs_tag` helper just to navigate. For library users this is a constant tax.

### 3.1 Proposed design

```julia
"""
    coproduct(ps::Polynomial...) -> Polynomial

n-ary disjoint union. Positions are flat-tagged as `(k, x)` where `k` is the
1-based operand index and `x` is a position from `ps[k]`.
"""
function coproduct(ps::Polynomial...) :: Polynomial

"""
    flatten_coproduct(p::Polynomial) -> Polynomial

Re-tag a left-associated chain of binary `+`s into the flat form produced
by `coproduct`. Detects nested `(1, (1, ...))` patterns and flattens.
Idempotent on already-flat polynomials.
"""
function flatten_coproduct(p::Polynomial) :: Polynomial
```

**Binary `+` is unchanged.** Reviewer was explicit that `+` is correct as-is for binary use; the n-ary chain is what hurts. `coproduct(p, q) ≡ p + q` semantically but not in tag structure — that's intentional and documented.

For lenses: `coproduct(fs::Lens...)` analogously, requiring each `f` has compatible domain tagging.

### 3.2 Tests

- `coproduct(p, q, r).positions` has tags `(1, _), (2, _), (3, _)` flat.
- `flatten_coproduct(p + q + r) == coproduct(p, q, r)`.
- `flatten_coproduct` is idempotent.
- `coproduct(p)` returns `p` unchanged (degenerate case).

---

## 4. First-class `Coalgebra` peer type

**Problem.** Coalgebras `α : Sy^S → p` are central in Spivak's framework — Moore machines, dynamical systems, terminal coalgebras (cofree comonoids). Today they exist only as lens constructions (`state_system`, `dynamical_system`, `moore_machine`). No formal `Coalgebra` struct, no morphism type, no `validate_coalgebra`.

### 4.1 Terminology — `Coalgebra` vs. `Comodule`

Important distinction the reviewer's writeup glosses over: a *p-coalgebra* (where `p` is just a polynomial functor) and a *c-comodule* (where `c` is a comonoid) are different things:

- **p-coalgebra** = a state space `S` with structure map `α : Sy^S → p`. No coassociativity law — just a structure map.
- **c-comodule** = a polynomial `X` with a coaction `λ : X → c.carrier ▷ X` satisfying counit and coassociativity laws against `c`'s eraser and duplicator.

The library already has comodules (`RightComodule`, `LeftComodule`, `Bicomodule`). What's missing is the coalgebra-of-an-endofunctor framing. Both are useful; they should not be conflated.

### 4.2 Proposed design

```julia
"""
    Coalgebra(carrier::PolySet, polynomial::Polynomial, structure::Lens)

A p-coalgebra: a state space `carrier = S` with a structure map
`structure : Sy^S → polynomial`.

Type-check: `structure.dom == state_system(carrier) && structure.cod == polynomial`.
"""
struct Coalgebra
    carrier::PolySet
    polynomial::Polynomial
    structure::Lens
end

validate_coalgebra(c::Coalgebra) -> Bool   # shape constraints only; no law
to_lens(c::Coalgebra) -> Lens
from_dynamical(d) -> Coalgebra             # bridge for legacy callers
```

**Coalgebra morphism**:

```julia
struct CoalgebraMorphism
    dom::Coalgebra
    cod::Coalgebra
    map::Lens   # Sy^{dom.carrier} → Sy^{cod.carrier}, must commute with structure maps
end

validate_coalgebra_morphism(f::CoalgebraMorphism) -> Bool
```

The commuting square is checked element-wise.

**Bridges** (do not break existing API):

```julia
moore_machine(...)      # unchanged signature, returns Lens (today's behavior)
moore_machine_coalgebra(...) :: Coalgebra   # new convenience constructor
Coalgebra(d::DynamicalSystem) -> Coalgebra  # promotion
```

### 4.3 What this does NOT replace

- `RightComodule`, `LeftComodule`, `Bicomodule` stay where they are — those are coalgebras-of-comonoids, a different (richer) structure.
- `state_system`, `dynamical_system`, `moore_machine` keep returning lenses for backward compatibility.

### 4.4 Tests

- `Coalgebra(carrier, p, structure)` rejects ill-shaped lenses.
- A Moore machine packaged as a `Coalgebra` round-trips through `to_lens`.
- A coalgebra morphism that commutes with structure maps validates; one that doesn't, doesn't.
- `Coalgebra` printing / display follows the same conventions as `Comonoid`.

---

## 5. `subst_targeted_lens` helper

**Problem.** When `cod = subst(p, q)`, the convenience `Lens` constructor still requires manual handling of the `(i, j̄)` position structure and `(a, b)` direction structure in the on-direction callback. Reviewer hit this for both coactions of every bicomodule.

### 5.1 Proposed design

```julia
"""
    subst_targeted_lens(dom::Polynomial, p::Polynomial, q::Polynomial,
                        on_pos::Function, on_dir::Function) -> Lens

Convenience constructor for a lens `dom → subst(p, q)` that handles the
(i, j̄) position decomposition and (a, b) direction decomposition.

Callbacks:
  on_pos(x) -> (i, j̄) where i ∈ p(1) and j̄ : p[i] → q(1)
  on_dir(x, a, b) -> dom_direction at x, where a ∈ p[i] and b ∈ q[j̄(a)]
"""
function subst_targeted_lens(dom, p, q, on_pos, on_dir) :: Lens
```

**Internal**: builds the `Lens` against the lazy `LazySubst(p, q)` codomain when item #1 is in (so type-check goes through `is_subst_of` without enumeration). Until #1 lands, builds against eager `subst(p, q)`.

### 5.2 Companion: `subst_targeted_coaction` for bicomodule callers

```julia
function subst_targeted_coaction(carrier, base_comonoid, on_pos, on_dir;
                                 side::Symbol = :left) :: Lens
```

Same as `subst_targeted_lens` but pre-fills `p`, `q` based on which side of the bicomodule you're constructing. Eliminates a class of typos at the call site.

### 5.3 Tests

- A bicomodule constructed with `subst_targeted_coaction` matches one constructed with the manual `Lens` form.
- Type-check failures (wrong arity in `on_pos`, wrong type in `on_dir`) produce structured error messages, not stack traces.

---

## 6. Structural validation diagnostics

**Problem.** `verbose=true` on `validate_*` prints which law failed and at which tuple. Reviewer's complaint: that doesn't tell you *why* in structural terms — "your duplicator's on-positions doesn't agree with your eraser's identity choices at object X" is more actionable than "Law 2 failed at (X, foo, bar)." For bicomodule compatibility failures specifically, a "minimal failing triple" reporter would help debugging immensely.

### 6.1 Proposed design — Bool API + `_detailed` companions

> **Implementation note (2026-04-28):** the original Q6 resolution was "soft widening with `Base.convert(::Type{Bool}, ::ValidationResult)`." On test, this proved incompatible with `Test.jl`'s `@test` macro, which checks `isa(value, Bool)` directly and treats anything else as a non-boolean error. Rather than fight `Test.jl`, the implementation kept `validate_*` returning `Bool` for back-compat and added `validate_*_detailed` companions returning `ValidationResult`. The structural-failure information is fully preserved; access pattern just differs.

```julia
struct ValidationResult
    passed::Bool
    failures::Vector{ValidationFailure}
    summary::String
end

struct ValidationFailure
    law::Symbol            # :counit_left, :counit_right, :coassoc, :compatibility, ...
    location::Tuple        # the (object, direction, ...) tuple where it broke
    structural_hint::String # "duplicator's on-positions disagrees with eraser at $X"
    actual::Any
    expected::Any
end

# Bool conversion preserves existing call sites:
Base.convert(::Type{Bool}, r::ValidationResult) = r.passed
Base.:(!)(r::ValidationResult) = !r.passed
```

`if validate_comonoid(c) ... end` keeps working because `Bool(::ValidationResult)` exists. New code can inspect `r.failures`.

### 6.2 Structural hints — where they come from

For `validate_comonoid`:
- **Counit law fails on positions at `i`**: hint = "eraser maps position $i to $(eraser_image), duplicator's first projection at position $i maps to $(dupl_first_image); these should agree."
- **Coassociativity fails at `(i, a, b)`**: hint = "left-then-right path gives $left, right-then-left gives $right; the duplicator's nesting at $i, $a is asymmetric."

For `validate_bicomodule`:
- Compatibility-positions failure: hint identifies *which* of the two coaction paths produced the mismatch and at which level (position vs. direction).
- **Minimal failing triple**: when verbose, search for the lex-smallest `(x, b, a)` triple where the compatibility square fails. Report that, not the first one encountered. (Implementation: collect all failures, sort lexicographically, return the head.)

### 6.3 `verbose` semantics

- `verbose = false` (default): return `ValidationResult` with `failures` populated but no printing.
- `verbose = true`: also pretty-print failures with structural hints to stderr.
- `verbose = :first`: stop at first failure (today's behavior).
- `verbose = :all`: collect every failure (new — useful for big diagnostic dumps).

### 6.4 Migration

- All existing `validate_*` keep their `(args...; verbose) -> Bool`-shaped call signature.
- Internally they construct `ValidationResult` and rely on the `Bool` conversion.
- New helper `validate_*_detailed(args...) -> ValidationResult` exposes the full result.

### 6.5 Tests

- A `ValidationResult` with `passed = true` is truthy.
- A failing comonoid produces a failure whose `structural_hint` mentions the specific component.
- A failing bicomodule reports the lex-smallest triple, not just any triple.

---

## 7. `TABULATE_SIZE_CAP` error message

**Problem.** `TABULATE_SIZE_CAP = 10^5` is a sensible default; reviewer hit it once during exploration. The current message (`PolyFunctions.jl:44–48`) does mention `force=true`, but doesn't surface the other paths.

### 7.1 Proposed design — message-only change, no API change

Rewrite the error message to enumerate the four escape hatches:

```
Domain has $(c.n) elements (> TABULATE_SIZE_CAP[] = $(TABULATE_SIZE_CAP[])).

Options:
  1. Pass `force = true` to tabulate this function anyway.
  2. Raise the global cap: `Poly.set_tabulate_cap!($(c.n) + 1)`.
  3. Use structural equality where applicable (see `is_subst_of`,
     `is_isomorphic`) to avoid materializing.
  4. Construct the function manually as a `Dict`-backed `PolyFunction`
     and pass it directly.
```

Add a new public setter `set_tabulate_cap!(n::Int)` that wraps the `Ref` mutation, since touching the `Ref` directly works but is awkward.

### 7.2 Tests

- Triggering the error captures stderr and asserts all four bullets are present.
- `set_tabulate_cap!(10)` then `set_tabulate_cap!(10^5)` round-trips.

---

## 8. Symbolic ↔ concrete interop polish

**Problem.** Reviewer notes that mixed-mode work needs explicit `lift` and `evaluate`, with a sharp boundary. They explicitly flagged this as "probably an intentional design choice — symbolic shouldn't silently pollute concrete computation — but worth noting."

### 8.1 Position taken: keep the boundary sharp, document it loudly

The sharpness *is* the right design. Symbolic polynomials carry semantics that concrete Julia values can't pin down (variables, deferred operations). Silent promotion would create surprising correctness bugs. We keep `lift` and `evaluate` explicit.

### 8.2 What we add

- **Consistent helper names**: `to_symbolic(::Polynomial) = lift(...)`, `to_concrete(::SymbolicPolynomial, env) = evaluate(...)`. The current names stay; the new ones are aliases. Concrete↔Symbolic intent is clearer than `lift`/`evaluate`, which feel like generic combinators.
- **Promotion rules in arithmetic**: `+(p::Polynomial, s::SymbolicPolynomial) -> SymbolicPolynomial` (downcasting concrete to symbolic for the operation, never the reverse). Defined for `+`, `*`, `⊗`, `▷`. This isn't silent promotion of the *result* — the result type makes the symbolic-ness obvious — but it removes the "I have to lift everything by hand to write `p + sq`" friction.
- **Documentation tour**: a new `docs/literate/08_interop.jl` walking through the boundary, when to lift, when to evaluate, what the trade-offs are.

### 8.3 What we explicitly do *not* do

- `==` between concrete and symbolic. Different worlds; comparing them is a category error. Use `sym_equal` or explicit `evaluate` first.
- Implicit re-concretization on assignment.

### 8.4 Tests

- `Polynomial + SymbolicPolynomial` returns a `SymbolicPolynomial`.
- The new helper names produce the same result as `lift`/`evaluate`.

---

## 9. Examples coverage

**Problem.** Examples folder is biased toward Moore machines (`moore_machine_simulation.jl`, `cofree_behavior_tree.jl` with `:go`/`:stop`). Bicomodule construction, retrofunctors between non-trivial categories, and cofree-comonoid use *in earnest* are absent.

### 9.1 Three new examples

**`bicomodule_walk.jl`** — a non-trivial bicomodule: take two distinct comonoids `C` and `D`, build a `C → D` bicomodule whose carrier *isn't* `regular_bicomodule(C)`. Concretely: `C` is a 3-object linear category, `D` is a 2-object category with a swap, the bicomodule expresses a "translation" between them. Validates, prints a polybox, walks through one composition step.

**`retrofunctor_categories.jl`** — go beyond the existing `retrofunctor_walk.jl`'s phase lift. Build a retrofunctor from a graph category to a tree-shaped category (collapsing branches). Validate, show the comonoid morphism it induces, exhibit the structural difference from a "naive" functor.

**`cofree_in_anger.jl`** — use `cofree_comonoid` for what it's actually for: build a small process polynomial `p`, take its cofree comonoid `T_p`, and use the universal property to lift a coalgebra `Sy^S → p` to a retrofunctor `S → T_p`. This is the real Ch. 8 punchline and it's currently absent from examples.

### 9.2 Dependencies

- `bicomodule_walk.jl` depends on #1 (otherwise the construction is too slow to be a tutorial).
- `retrofunctor_categories.jl` depends on #2 (for `+` on comonoids — both example categories are built as coproducts of simpler ones).
- `cofree_in_anger.jl` depends on #4 (uses `Coalgebra` to package the structure map).

### 9.3 Tests

- All three examples run end-to-end without errors as part of `run_all_demos.jl`.
- Each example's output is committed as a golden file for diff-detection.

---

## 10. Cross-cutting concerns

### 10.1 Backward compatibility

- Every existing public API keeps working. Items #1–#9 are additive or soft-additive (return type widening with `Bool` conversion in #6).
- One exception: §1.2 option (i) introduces `AbstractPolynomial`, which means user code that pattern-matches on `::Polynomial` keeps working but user code that *constructs* abstract types changes. We commit to the alias `const Polynomial = ConcretePolynomial` (or similar) to keep names stable.

### 10.2 Semver

- The whole batch is a minor version bump (`0.1.0 → 0.2.0`) since some return types widen. No major.

### 10.3 Documentation

- Every new public symbol gets a docstring with a Niu/Spivak chapter reference, matching existing convention.
- New tour `docs/literate/08_interop.jl` for #8.
- `docs/dev/extensions_v1_design.md` (this file) is preserved as the historical record of decisions.

### 10.4 Test infrastructure

- New test file per item: `test/test_extensions_lazy_subst.jl`, `test/test_extensions_comonoid_ops.jl`, etc.
- Each PR adds its test file and updates `runtests.jl` to include it.

---

## 11. Dependency graph and PR ordering

```
              ┌────────────────────┐
              │ #1 Lazy subst      │ ◄── unblocker for #2, #5, #9
              └─────────┬──────────┘
                        │
        ┌───────────────┼───────────────┐
        ▼               ▼               ▼
  ┌──────────┐    ┌──────────┐    ┌──────────┐
  │ #2 Mon.  │    │ #5 helpr │    │ #9 (part)│
  │ ops      │    │          │    │          │
  └──────────┘    └──────────┘    └──────────┘

  ┌──────────┐    ┌──────────┐    ┌──────────┐
  │ #4 Coalg │    │ #6 diags │    │ #3 n-ary │   (independent of each other)
  └──────────┘    └──────────┘    └──────────┘

  ┌──────────┐    ┌──────────┐
  │ #7 cap   │    │ #8 sym↔c │   (independent, polish)
  └──────────┘    └──────────┘
```

**Recommended PR order:**

1. **#1 (lazy subst)** — unblocks the most. Smallest version: just `is_subst_of` + Bicomodule constructor switch. Defer Layer B/C to a follow-on PR if the diff gets too big.
2. **#7 (cap message)** — trivial, lands while #1 is in review.
3. **#3 (n-ary coproduct)** — also small and independent.
4. **#6 (diagnostics)** — touches every validator; do early so later PRs benefit.
5. **#4 (Coalgebra)** — independent, can land in parallel with #6.
6. **#2 (monoidal operators on Comonoid/Bicomodule)** — the largest piece of new math.
7. **#5 (subst_targeted_lens)** — depends on #1 settling.
8. **#8 (interop polish)** — small, lands late.
9. **#9 (examples)** — last, exercises everything that came before.

---

## 12. Final status (v0.2.0 ship)

All eight design questions resolved. PRs #1–#8 shipped; PR #9 deferred per
the maintainer's call.

### Resolved

- **(Q1)** `AbstractPolynomial` supertype with `Polynomial` const alias to
  `ConcretePolynomial`. (PR #1)
- **(Q2)** All three layers of lazy subst landed in PR #1: `is_subst_of`,
  `LazySubst`, lazy composition.
- **(Q3)** Both `*` and `⊗` exposed on Comonoid. (PR #2)
- **(Q4)** Both `compose` and Unicode `⊙` exposed on Bicomodule. (PR #2)
- **(Q5)** `Coalgebra` carrier is `PolySet`. (PR #4)
- **(Q6)** `ValidationResult` exposed via `validate_*_detailed` companions
  rather than soft Bool conversion (the original plan didn't survive
  `Test.jl`'s `isa Bool` check; see §6.1 implementation note). (PR #6)
- **(Q7)** Auto-promote in arithmetic, equality stays explicit. (PR #8)
- **(Q8)** PR #9 examples deferred per maintainer's call.

### Shipped in v0.2.0

- PR #1 — Lazy subst (all three layers).
- PR #2 — Comonoid `+`, `*`, `⊗`; Bicomodule `+`, `⊗`, `compose` / `⊙`.
- PR #3 — n-ary `coproduct` and `flatten_coproduct`.
- PR #4 — First-class `Coalgebra` and `CoalgebraMorphism`.
- PR #5 — `subst_targeted_lens` and `subst_targeted_coaction`.
- PR #6 — `ValidationResult` / `ValidationFailure` / `minimal_failing_triple`,
  with `_detailed` companions on every validator and `verbose=:all` mode.
- PR #7 — Improved `TABULATE_SIZE_CAP` error message + `set_tabulate_cap!`.
- PR #8 — Symbolic↔concrete arithmetic promotion + `to_symbolic` /
  `to_concrete` aliases + `docs/literate/08_interop.jl` tour.

### Deferred to v1.1 (with rationale)

- **Full coequalizer for `compose(::Bicomodule, ::Bicomodule)`.** The
  current implementation is exact for regular bicomodules and most
  practical cases. Closing the general case requires Niu/Spivak Def. 8.31's
  precise equivalence rule, which warrants a focused PR with the book at
  hand and verification against the unit law on non-trivial examples.
  Flagged inline in `Cofree.jl`'s compose docstring.
- **Widen `Lens.dom` and `Lens.cod` to `AbstractPolynomial`.** Would let
  `subst_targeted_lens` return a lens with a `LazySubst` cod, fully
  avoiding the eager `subst(...)` materialization. Touches every method
  on `Lens` that types `cod` or `dom` — composition, equality,
  validation, Sprint 5/6 code. Deferred to a standalone PR with
  comprehensive regression testing.
- **PR #9 examples** (`bicomodule_walk`, `retrofunctor_categories`,
  `cofree_in_anger`). Existing Sprint 1–8 examples cover the basics; the
  v0.2.0 docstrings carry the new APIs.

### What changed mid-implementation

Two implementation notes worth surfacing for future readers:

1. **§6.1 ValidationResult — Bool conversion abandoned.** The original
   Q6 plan was "soft widening with `Base.convert(::Type{Bool}, ...)`" so
   `@test validate_*(c)` would just work. In practice `Test.jl`'s `@test`
   checks `isa(value, Bool)` directly and reports non-Booleans as test
   errors. The implementation kept `validate_*` returning `Bool` and
   exposed the structured result via `_detailed` companions. Net effect
   is the same (structural failure information available) with cleaner
   types.

2. **§2.3 Bicomodule `⊗` base encoding.** The user-facing `Comonoid ⊗`
   goes through `to_category` → categorical product → `from_category`,
   producing a comonoid whose carrier polynomial has morphism-pair
   directions. For `Bicomodule ⊗`, the bases need direction-pair
   encoding to align with `Polynomial ⊗`'s carrier tensor; an internal
   helper `_comonoid_carrier_tensor` builds those. The two tensor
   constructions are isomorphic but encode directions differently. See
   the comment block in `Cofree.jl`'s parallel-of-bicomodules section.
