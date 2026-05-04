# Poly.jl → PolyAggregation.jl handoff

> **Status**: SKETCH, last updated 2026-05-04. Travels with the PolyAggregation.jl repo when it spins up — at that point this file is copied to PolyAggregation.jl's `docs/dev/extensions_v1_design.md` and the section on "what core needs to do first" is replaced by a "what core has done" status table.
>
> **As of 2026-05-04:** all v0.6 + v0.6.1 prereqs are **shipped to `main`** of Poly.jl with tests green. PolyAggregation v0.2.0 + v0.3.0 are unblocked. The only outstanding Poly-side dependency is multi-variable Dirichlet ⊗ on `d-Set[c]` (Lemma 7.13), needed for PolyAggregation v0.4 / Theorem 8.8's full categorical realization but **not** for v0.2.0 or v0.3.0.

---

## 0. Why a separate library

PolyAggregation.jl implements §8 of Spivak/Garner/Fairbanks, *Functorial Aggregation* (arXiv 2111.10968v7) — database aggregation (GROUP BY, sum-by-key, count, etc.) as a module homomorphism in `Cat♯_lin`. It depends on Poly.jl but doesn't belong inside it, for the same reasons PolyMarkov.jl is separate:

- **Domain weight.** Schemas, instances, commutative-monoid registries, aggregator functors `Fin → Set` — all of these are concepts that are meaningful only in the database / aggregation context. Putting them in Poly.jl core would force every Poly.jl user to scroll past them.
- **Dependency creep.** Aggregation eventually wants to talk to actual storage (CSV, SQLite, DataFrames.jl). None of that should be a transitive dependency of "I want to do polynomial functor algebra in Julia."
- **Independent cadence.** Database semantics evolve faster than the categorical foundations. Splitting lets PolyAggregation iterate on aggregator design without being held to Poly.jl's release cadence, and lets Poly.jl iterate on category-theoretic primitives without breaking PolyAggregation's API contract.

The dependency arrow is **strictly one-way**: `PolyAggregation.jl → Poly.jl`. Poly.jl never imports anything from PolyAggregation.

---

## 1. What Poly.jl needs to ship before PolyAggregation.jl can start

Aggregation rests on machinery that must be in core *first*. This table is the gating list.

| Capability | Paper section | Poly.jl version | Status |
|---|---|---|---|
| `Bicomodule`, `Comonoid`, `Lens`, `compose` for ◁ | §2-5 | v0.5 | ✓ in main |
| `LinearBicomodule` wrapper + `is_linear` predicate | §6 | **v0.5.1** | ✓ shipped |
| List polynomial `u = Σ_N y^N` (polynomial only) | Def 8.6 | **v0.5.1** | ✓ shipped (function form `list_polynomial(; max_size)`) |
| `linear_bicomodule_from_span(C, D, S, s, t)` (forward, discrete bases) | Cor 6.17 | **v0.5.1** | ✓ shipped |
| `c_one_y(c)` Theorem 8.8 carrier | §8.1 | **v0.5.1** | ✓ shipped (as c-1 bicomodule, see §1.1 below) |
| `morphisms_out_of` + `cod_in_comonoid` ergonomics | — | **v0.5.1** | ✓ shipped |
| `bridge_diagram` introspection (linear-case projection) | Prop 3.20 | **v0.6** | ✓ shipped |
| `bridge_diagram` full `(B, E, π, S, T)` form | Prop 3.20 | **v0.7-partial** | ✓ shipped (set-level; categorical structure on E pending v0.7-main) |
| `is_conjunctive` + `ConjunctiveBicomodule` | Cor 6.15 | v0.7-main | not started (deferred from v0.6 as not blocking PolyAggregation v0.3.0) |
| `weak_dual(p)` (single-var Dirichlet) | Example 7.2 | **v0.6** | ✓ shipped (alias for `internal_hom(p, y)`) |
| `is_reflexive(p)` | Example 7.2 | **v0.6.1** | ✓ shipped |
| `coclosure(q, p)` (FA Prop 2.16, finite case) | Prop 2.16 | **v0.6.1** | ✓ shipped |
| `comonoid_from_coclosure(p)` (FA Example 5.5) | Example 5.5 | **v0.6.1** | ✓ shipped |
| `comonoid_from_list_polynomial(u)` (real, on `[u/u]` per Lemma 8.7) | Lemma 8.7 | **v0.6.1** | ✓ shipped (requires `max_size`; symbolic case in v0.7-main) |
| `span_from_linear_bicomodule` (reverse direction, NamedTuple) | Cor 6.17 reverse | **v0.6** | ✓ shipped |
| `Span{A,B}` struct + finite-set pullback in `compose(::Span, ::Span)` | Cor 6.17 | v0.7-main+ | not started (deferred from v0.6 as not blocking PolyAggregation v0.3.0) |
| **Multi-variable Dirichlet ⊗ on `d-Set[c]`** | §7.2-7.3, Lemma 7.13 | **v0.7-main** | designed (`extensions_v6_design.md` §1) |
| **Cat♯ left Kan extensions** for general `(c,d)` | Prop 6.7 | **v0.7-main** | designed (`extensions_v6_design.md` §4) |
| **Theorem 7.19 contravariant equivalence** | §7, Eq. 64 | **v0.7-main** | designed (`extensions_v6_design.md` §2) |
| **Profunctor ↔ conjunctive bicomodule dictionary** | Prop 7.25, 7.27 | **v0.7-main** | designed (`extensions_v6_design.md` §3) |
| **Module homomorphism types** in Cat♯_lin | §6, §7.3.1 | **v0.7-main** | partially shipped (LinearBicomodule + bridge); full module shipped with #2 |
| **Symbolic coclosure** for `coclosure(list_polynomial(), list_polynomial())` | extends Prop 2.16 | **v0.7-main** | designed (`extensions_v6_design.md` §6) |
| **Theorem 8.8** universal-property machinery | §8 | already implicit | sufficient when above land |

### 1.1 v0.5.1 deviations from the original plan (read before adopting)

Two corrections were forced during v0.5.1 implementation by tracing through `validate_bicomodule_detailed`. Important if you wrote PolyAggregation against the original sketch:

- **`c_one_y(c)` returns a c-1 bicomodule, not c-c.** The right base is `discrete_comonoid(FinPolySet([:pt]))` (the unit comonoid), not `c` itself. With the cod-tracking left action required for non-discrete `c`, the bicomodule compatibility law forces the right action to be constant in the carrier-position; the unit comonoid is the cleanest right base that satisfies this. PolyAggregation only needs the left c-action for `↻^α : c(1)y ◁ c → c(1)y`, so this packaging is functionally equivalent for the consumer. Adapt: replace any `c_one_y(c).right_base === c` assertion with `cardinality(positions(c_one_y(c).underlying.right_base.carrier)) == Finite(1)` or just don't read the right base.

- **`linear_bicomodule_from_span` uses trivial action**. Result satisfies `validate_bicomodule` for *discrete* C and D — the natural PolyAggregation use case. For non-discrete bases, construction succeeds but the bicomodule axioms aren't generally satisfied. The fuller treatment via bridge diagrams ships in v0.6.

### 1.2 v0.5.1 unblocks PolyAggregation v0.2.0 — start now

With v0.5.1 shipped (still awaiting a git tag, but on `main`), PolyAggregation can:

- Drop its v0.5-era stubs and import the real surface: `using Poly: list_polynomial, is_linear, LinearBicomodule, linear_bicomodule_from_span, c_one_y, morphisms_out_of, cod_in_comonoid`.
- Wire `list_aggregator()` to `list_polynomial()` as carrier — closes the data-vs-polynomial gap demonstrated in `examples/list_universal.jl`.
- Type `aggregate_along(inst, query::LinearBicomodule)` against the new wrapper.
- Use `c_one_y(schema.category)` as the carrier for `aggregate_morphism(::Instance)` (with the c-1 packaging caveat above).
- Replace the `aggregate(inst)` morphism walk's `direction_at` / `duplicator.on_positions` plumbing with `morphisms_out_of` + `cod_in_comonoid`.

Spinout is no longer gated on v0.7; v0.7 only gates **PolyAggregation v0.3** (full Theorem 8.8 categorical realization via multi-variable Dirichlet ⊗). Reserve the GitHub repo and start scaffolding the public package whenever you're ready.

What this means in practice:
- v0.5.1 unblocks PolyAggregation v0.2.0 (data-level `aggregate(::Instance)` working end-to-end on the four worked examples).
- v0.6 unblocks richer query types (conjunctive bicomodules, weak duals, full bridge-diagram introspection on non-discrete schemas).
- v0.7 unblocks PolyAggregation v0.3 — the multi-foreign-key aggregation Theorem 8.8 fully realizes.

---

## 2. What PolyAggregation.jl owns (the API surface)

Once Poly.jl v0.7 lands, PolyAggregation.jl should ship:

### 2.1 Aggregator functors

```julia
# An aggregator ↻_a : Fin → Set
struct AggregationFunctor
    apply::Function          # N::Int -> Set
    restrict::Function       # (f::Function{Int,Int}, N::Int, N'::Int) -> Function{Set, Set}
    is_commutative::Bool     # if true, behaves on FinBij rather than Fin
end

# Built-ins
sum_aggregator(M::CommutativeMonoid) :: AggregationFunctor      # ↻(N) = M^N
count_aggregator() :: AggregationFunctor                         # ↻(N) = ℕ, restrict via fiber sizes
list_aggregator() :: AggregationFunctor                          # ↻(N) = Σ_N y^N (the universal one)
mean_aggregator() :: AggregationFunctor                          # numerator + denominator pair
min_aggregator() :: AggregationFunctor
max_aggregator() :: AggregationFunctor
top_k_aggregator(k::Int) :: AggregationFunctor
```

The list aggregator is universal in the sense that any aggregator factors through it: aggregation = "collect into a list" + "fold the list with the aggregator's monoid op." So `list_aggregator` is the `u` polynomial from item #4 of the v0.6 work, repackaged in aggregator clothing.

### 2.2 Schemas and instances

```julia
struct Schema
    category::Comonoid                                   # the schema-as-category c
    aggregators::Dict{Position, AggregationFunctor}     # ↻_a per object of c
end

struct Instance
    schema::Schema
    data::Function                  # a -> FinSet,  the c-set X
    values::Dict{Position, Any}     # α_a ∈ ↻_a(X(a))
    function Instance(schema, data, values)
        validate_instance(schema, data, values) || error("invalid instance")
        new(schema, data, values)
    end
end

validate_instance(schema, data, values) :: Bool
```

A `Schema` is a small category (built using `free_labeled_transition_comonoid` from Poly.jl) plus an aggregator per object. An `Instance` is concrete data fitting that schema.

### 2.3 The aggregate operation

```julia
aggregate(inst::Instance) :: BicomoduleMorphism
# Builds the Theorem 8.8 module homomorphism c(1)y ◁ c → c(1)y
# realizing the instance's aggregation against the schema's aggregators

aggregate_along(inst::Instance, query::LinearBicomodule) :: Instance
# The interesting one: aggregate the instance through a query bicomodule
# (the categorical generalization of GROUP BY)

migrate_then_aggregate(inst::Instance, retro::Retrofunctor) :: Instance
# Schema migration along a retrofunctor, then aggregate
# Theorem from §8: this commutes with the obvious "aggregate then migrate" alternative
# under conditions the paper makes precise — useful regression test
```

### 2.4 Worked examples

PolyAggregation.jl should ship at least:
- A `examples/sql_groupby.jl` showing a small-table SQL-style GROUP BY equivalence.
- A `examples/sum_by_key.jl` reducing to standard `Dict{K, V}`-style aggregation.
- A `examples/migration_commutes.jl` exhibiting the schema-migration-vs-aggregation commutation theorem on a concrete example, plus a counterexample showing where it fails.
- A `examples/list_universal.jl` deriving sum/count/mean/min/max from `list_aggregator` by post-composition, demonstrating universality.

---

## 3. Boundary discipline

These rules govern what crosses the Poly.jl / PolyAggregation.jl boundary.

**Allowed across the boundary (Poly.jl → PolyAggregation.jl, import side):**
- All Poly.jl public types (`Polynomial`, `Lens`, `Comonoid`, `Bicomodule`, `Retrofunctor`, `LinearBicomodule`, `BicomoduleMorphism`, etc.)
- All Poly.jl public operations (`compose`, `parallel`, `kan_along_bicomodule`, `weak_dual`, `bridge_diagram`, `linear_bicomodule_from_span`, `list_polynomial`, etc.)
- The `validate_*` family
- Symbolic-set machinery (`SymbolicSet`, `Cardinality`, etc.) where needed for infinite aggregators

**Not allowed across the boundary (anything PolyAggregation.jl introduces stays in PolyAggregation.jl):**
- `AggregationFunctor`, `Schema`, `Instance`, `aggregate`, `migrate_then_aggregate` — these live in PolyAggregation.jl only.
- `CommutativeMonoid` — lives in PolyAggregation.jl. (If it turns out to be useful for PolyMarkov.jl too, factor out to a small `CategoricalAlgebra.jl`-style shared utility — but defer that until both libraries actually want it.)
- Any storage-backend types (CSV adapters, SQLite adapters, DataFrames.jl interop). PolyAggregation.jl owns these via optional sub-packages or extras.

**Forbidden in both directions:**
- Poly.jl types that depend on PolyAggregation.jl types (would create a cycle).
- PolyAggregation.jl monkey-patching Poly.jl methods.
- Type piracy — PolyAggregation.jl never extends a Poly.jl method on a Poly.jl-owned type unless the method itself is owned by PolyAggregation.jl.

If PolyAggregation.jl finds it needs a Poly.jl primitive that doesn't exist, the resolution is:
1. Open an issue on Poly.jl describing the use case.
2. Add the primitive to a future Poly.jl release.
3. PolyAggregation.jl bumps its `Poly` compat bound and uses the new primitive.

Never reach across by re-implementing the primitive locally.

---

## 4. Repo layout and tooling

```
PolyAggregation.jl/
├── Project.toml          # depends on Poly ≥ 0.7
├── README.md
├── src/
│   ├── PolyAggregation.jl
│   ├── AggregationFunctors.jl
│   ├── CommutativeMonoid.jl
│   ├── Schema.jl
│   ├── Instance.jl
│   ├── Aggregate.jl
│   └── Validation.jl
├── test/
│   ├── runtests.jl
│   ├── test_aggregators.jl
│   ├── test_schema.jl
│   ├── test_instance.jl
│   ├── test_aggregate.jl
│   └── test_migration_commutes.jl
├── examples/
│   ├── sql_groupby.jl
│   ├── sum_by_key.jl
│   ├── migration_commutes.jl
│   └── list_universal.jl
└── docs/
    ├── make.jl
    └── src/
        ├── index.md
        ├── concepts.md
        ├── api.md
        └── examples.md
```

Reuse Poly.jl's tooling choices: Documenter + Literate, the same CI matrix (Julia 1.10, 1.11), the same coverage / linting setup. The build-time gotchas already known to Poly.jl (`remotes=nothing`, null-byte padding for Documenter on Windows) carry over verbatim.

---

## 5. Initial release plan

**v0.1.0** — first working slice. Includes: `AggregationFunctor` with sum/count/list, `Schema`/`Instance` types, `aggregate(::Instance)`, the four worked examples. No advanced operations.

**v0.2.0** — schema migration. Adds `migrate_then_aggregate`, the commutation theorem witness, additional aggregators (mean, min, max, top-k).

**v0.3.0** — composition. Adds composition of aggregations, equivalent of nested GROUP BY, multiple-aggregator schemas.

**v0.4.0+** — storage adapters in optional sub-packages: `PolyAggregationCSV.jl`, `PolyAggregationDataFrames.jl`, etc.

Time estimate to v0.1.0: ~2-3 weeks of focused work *after* Poly.jl v0.7 is on `main`. So calendar-wise: probably late v0.7 cycle or early v0.8.

---

## 6. Open questions that travel with the spinout

These are the questions that should be marked "for PolyAggregation.jl design round 1" rather than answered here:

**QA1.** Is `AggregationFunctor` a struct (data) or an abstract type with concrete subtypes (sum, count, ...)? The struct version is more flexible; the subtype version dispatches faster and gives better error messages. Recommendation deferred.

**QA2.** How does `Instance.values` get typed? `Dict{Position, Any}` is honest about the heterogeneity but loses static checking; a parametric `Instance{V}` with `values::Dict{Position, V}` is more ergonomic when all aggregators target the same monoid. Probably ship `Any` first, parameterize later.

**QA3.** Does `aggregate` return a `BicomoduleMorphism`, an `Instance`, or both via different methods? The paper says morphism; a user typically wants the resulting instance. Probably both, with `aggregate(inst)` returning the instance and `aggregate_morphism(inst)` returning the morphism for the categorically-minded.

**QA4.** What's the relationship to existing Julia database libraries (DataFrames.jl, Query.jl, SQLite.jl)? Optional adapter packages from v0.4 onward, no core dependency.

**QA5.** Should commutative-