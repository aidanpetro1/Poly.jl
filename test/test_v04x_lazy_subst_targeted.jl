# ============================================================
# v0.4.x patch: subst_targeted_lens builds a lazy codomain
# ============================================================
#
# Spec: PolyCDS deep-modularity follow-up (2026-05-02).
#
# `subst_targeted_lens(dom, p, q, ...)` previously built its codomain via
# eager `subst(p, q)`, which materializes `Σ_i |q(1)|^|p[i]|` positions.
# For the v0.4.x base_change_left/right paths on PolyCDS-style inputs
# (`subst(C0, M.carrier)` where M.carrier is a tensored bicomodule
# carrier) this exploded to ~10^12 positions and hung Julia mid-Dict
# construction.
#
# Fix: swap to `subst_lazy(p, q)`, mirroring the v0.4.0 lazy-everywhere
# policy and the cofree_comonoid duplicator perf fix in the same release.
#
# Tests cover:
#
#   1. Structural laziness — cod is a `LazySubst`; `positions(cod)` is a
#      `SubstPolySet`; cardinality reports the expected `Σ_i |q|^|p[i]|`
#      without enumeration.
#   2. No materialization on a fixture whose eager `subst(p, q)` would
#      have ~10^7 positions. Construction returns immediately; before
#      the fix this would have materialized millions of jbar dicts.
#   3. `is_subst_of` accepts the lazy cod via the lazy short-circuit
#      (no `force_enumerate` needed).
#   4. Cross-type `lens.cod == subst(p, q)` still passes for the small
#      cases existing tests rely on (Monoidal.jl:752 cross-type method).
#   5. `subst_targeted_coaction` propagates laziness — both `:left` and
#      `:right` sides return lenses with `LazySubst` codomains.
#   6. End-to-end: a `Bicomodule` constructed via `subst_targeted_lens`
#      coactions succeeds (constructor's `is_subst_of` shape-check
#      short-circuits without forcing the lazy operands).
#   7. Behavioral equivalence — direction routing is unchanged. The
#      eager-built and lazy-built lenses agree extensionally on every
#      `(x, (a, b))` input the smaller fixture admits.

@testset "v0.4.x: subst_targeted_lens uses lazy cod" begin

    # ------------------------------------------------------------
    # 1. Structural laziness: cod is a LazySubst
    # ------------------------------------------------------------
    @testset "cod is a LazySubst (structural)" begin
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:u]) : FinPolySet([:v]))
        dom = Polynomial(FinPolySet([:x]), _ -> FinPolySet([:dx]))
        f = subst_targeted_lens(dom, p, q,
                _ -> (:i1, Dict(:a => :j1, :b => :j2)),
                (_, _, _) -> :dx)
        @test f.cod isa LazySubst
        @test f.cod.p === p
        @test f.cod.q === q
        @test positions(f.cod) isa Poly.SubstPolySet
    end

    # ------------------------------------------------------------
    # 2. No eager materialization on a would-be-large subst
    # ------------------------------------------------------------
    @testset "no eager materialization on large operands" begin
        # p = y^10 (one position, direction-set of size 10).
        # q = constant of size 5 (5 positions, empty direction-sets).
        # eager subst(p, q) has 5^10 = 9_765_625 positions — would
        # construct ~10M jbar dicts at materialization time. With the
        # lazy fix this construction returns immediately.
        p = representable(FinPolySet(1:10))
        q = constant(FinPolySet([:a, :b, :c, :d, :e]))
        dom = Polynomial(FinPolySet([:x]), _ -> FinPolySet(Symbol[]))

        f = subst_targeted_lens(dom, p, q,
                _ -> (:pt, Dict(k => :a for k in 1:10)),
                (_, _, _) -> error("vacuous: no dom-directions"))

        @test f.cod isa LazySubst
        # Cardinality is computed via the algebra, not enumeration:
        # `Σ_i |q(1)|^|p[i]| = 5^10`. This call would not return in
        # reasonable time if it had to enumerate.
        c = cardinality(positions(f.cod))
        @test c == Finite(5)^Finite(10)
        @test c == Finite(9_765_625)
    end

    # ------------------------------------------------------------
    # 3. is_subst_of short-circuits on the lazy cod
    # ------------------------------------------------------------
    @testset "is_subst_of accepts the lazy cod via short-circuit" begin
        p = Polynomial(FinPolySet([:i]),
                       _ -> FinPolySet([:a, :b]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:u]) : FinPolySet([:v]))
        dom = Polynomial(FinPolySet([:x]), _ -> FinPolySet([:dx]))
        f = subst_targeted_lens(dom, p, q,
                _ -> (:i, Dict(:a => :j1, :b => :j2)),
                (_, _, _) -> :dx)
        # The decision-procedure's first step (lazy short-circuit on
        # operand identity) returns true without touching positions.
        @test is_subst_of(f.cod, p, q)
        # Mismatched operands still rejected.
        q2 = Polynomial(FinPolySet([:k]), _ -> FinPolySet([:w]))
        @test !is_subst_of(f.cod, p, q2)
    end

    # ------------------------------------------------------------
    # 4. Cross-type `lens.cod == subst(p, q)` still works
    # ------------------------------------------------------------
    @testset "cod == eager subst(p, q) via cross-type ==" begin
        # Backward-compat for the existing `test_extensions_subst_targeted.jl`
        # invariants. Cross-type `==(LazySubst, ConcretePolynomial)` in
        # Monoidal.jl materializes the lazy side and compares structurally.
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        q = Polynomial(FinPolySet([:j]), _ -> FinPolySet([:b]))
        dom = Polynomial(FinPolySet([:x]), _ -> FinPolySet([:dx]))
        f = subst_targeted_lens(dom, p, q,
                _ -> (:i, Dict(:a => :j)),
                (_, _, _) -> :dx)
        @test f.cod == subst(p, q)
        @test subst(p, q) == f.cod
    end

    # ------------------------------------------------------------
    # 5. subst_targeted_coaction propagates laziness on both sides
    # ------------------------------------------------------------
    @testset "subst_targeted_coaction inherits lazy cod" begin
        S = FinPolySet([:s1, :s2])
        c = state_system_comonoid(S)
        carrier = c.carrier
        dup_left = subst_targeted_coaction(carrier, c,
                s -> (s, Dict(t => t for t in S.elements)),
                (s, a, b) -> b;
                side = :left)
        @test dup_left.cod isa LazySubst
        @test is_subst_of(dup_left.cod, c.carrier, carrier)

        dup_right = subst_targeted_coaction(carrier, c,
                s -> (s, Dict(t => t for t in S.elements)),
                (s, a, b) -> b;
                side = :right)
        @test dup_right.cod isa LazySubst
        @test is_subst_of(dup_right.cod, carrier, c.carrier)
    end

    # ------------------------------------------------------------
    # 6. End-to-end: Bicomodule constructor accepts lazy coaction cods
    # ------------------------------------------------------------
    @testset "Bicomodule constructor accepts lazy coaction cods" begin
        # The regular bicomodule of a small comonoid: build its left/right
        # coactions via subst_targeted_lens. The constructor's
        # `is_subst_of` check must short-circuit on the LazySubst cod.
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        λL = subst_targeted_coaction(cs.carrier, cs,
                s -> (s, Dict(t => t for t in S.elements)),
                (s, a, b) -> b;
                side = :left)
        λR = subst_targeted_coaction(cs.carrier, cs,
                s -> (s, Dict(t => t for t in S.elements)),
                (s, a, b) -> b;
                side = :right)
        B = Bicomodule(cs.carrier, cs, cs, λL, λR)
        @test B isa Bicomodule
        @test validate_bicomodule(B)
    end

    # ------------------------------------------------------------
    # 7. Behavioral equivalence: eager-vs-lazy lenses agree extensionally
    # ------------------------------------------------------------
    @testset "lazy-built lens behaves identically to manual eager build" begin
        # The cross-type `Lens ==` test already lives in
        # test_extensions_subst_targeted.jl ("matches manual Lens
        # construction"); here we double-check direction-routing
        # extensionally on a fixture with non-trivial (a, b) pairs.
        p = Polynomial(FinPolySet([:i]),
                       _ -> FinPolySet([:a1, :a2]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:b1]) : FinPolySet([:b2]))
        dom = Polynomial(FinPolySet([:x]),
                          _ -> FinPolySet([:any]))
        f_helper = subst_targeted_lens(dom, p, q,
                _ -> (:i, Dict(:a1 => :j1, :a2 => :j2)),
                (_, a, b) -> :any)
        f_manual = Lens(dom, subst(p, q),
                        _ -> (:i, Dict(:a1 => :j1, :a2 => :j2)),
                        (_, ab) -> :any)
        # Lens equality across the lazy/eager cod boundary uses the
        # cross-type `_struct_equal(LazySubst, ConcretePolynomial)`
        # path, which materializes once and structurally compares.
        @test f_helper == f_manual
        # And direction routing matches at every (a, b) input.
        for ab in ((:a1, :b1), (:a2, :b2))
            @test f_helper.on_directions.f(:x).f(ab) ==
                  f_manual.on_directions.f(:x).f(ab)
        end
    end

end  # @testset "v0.4.x: subst_targeted_lens uses lazy cod"
