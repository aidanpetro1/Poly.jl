# ============================================================
# v0.5.1 — Minimum surface for PolyAggregation.jl
# ============================================================
#
# Five additive items per `docs/dev/extensions_v5_design.md`:
#   1. list_polynomial(; max_size)                         — Demos.jl
#   2. is_linear(::Bicomodule) + LinearBicomodule          — CatSharp.jl
#   3. linear_bicomodule_from_span                         — CatSharp.jl
#   4. c_one_y(::Comonoid)                                 — CatSharp.jl
#   5. morphisms_out_of + cod_in_comonoid                  — Comonoid.jl
#
# Tests exercise the public surface of each item and the discrete-comonoid
# round-trip between #3 and #4. Wider integration is left to PolyAggregation
# v0.2.0's own test suite.

@testset "v0.5.1: PolyAggregation minimum surface" begin

    # ----------------------------------------------------------
    # #5 morphisms_out_of / cod_in_comonoid (Comonoid ergonomics)
    # ----------------------------------------------------------
    @testset "morphisms_out_of / cod_in_comonoid" begin
        c = free_labeled_transition_comonoid([:a, :b], [(:a, :f, :b)])

        # Out-set at :a contains the identity (empty path) and f.
        out_a = morphisms_out_of(c, :a)
        @test out_a isa Vector
        @test length(out_a) == 2
        @test () in out_a
        @test (:f,) in out_a

        # Out-set at :b is just the identity.
        out_b = morphisms_out_of(c, :b)
        @test length(out_b) == 1
        @test out_b == [()]

        # Codomains: identity stays put, f goes :a → :b.
        @test cod_in_comonoid(c, :a, ())     == :a
        @test cod_in_comonoid(c, :a, (:f,))  == :b
        @test cod_in_comonoid(c, :b, ())     == :b

        # Errors when f is not in the out-set at a.
        @test_throws ErrorException cod_in_comonoid(c, :a, (:nonexistent,))
        @test_throws ErrorException cod_in_comonoid(c, :b, (:f,))

        # Discrete comonoid: each object has only the identity (:pt).
        cd = discrete_comonoid(FinPolySet([:x, :y_, :z]))
        @test morphisms_out_of(cd, :x) == [:pt]
        @test cod_in_comonoid(cd, :x, :pt) == :x
        @test cod_in_comonoid(cd, :y_, :pt) == :y_
    end

    # ----------------------------------------------------------
    # #1 list_polynomial — Def 8.6, polynomial only (no monad / [u/u] yet)
    # ----------------------------------------------------------
    @testset "list_polynomial" begin
        # Finite truncation: Σ_{N=0..5} y^N.
        u = list_polynomial(max_size=5)
        @test u isa AbstractPolynomial
        @test cardinality(positions(u)) == Finite(6)        # {0, 1, 2, 3, 4, 5}
        @test cardinality(direction_at(u, 0)) == Finite(0)
        @test cardinality(direction_at(u, 3)) == Finite(3)
        @test direction_at(u, 3) == FinPolySet([1, 2, 3])
        @test direction_at(u, 0) == FinPolySet(Int[])

        # Infinite default: positions are CountablyInfinite, direction-at-N
        # is still finite for any concrete N.
        u_inf = list_polynomial()
        @test cardinality(positions(u_inf)) == CountablyInfinite()
        @test cardinality(direction_at(u_inf, 7)) == Finite(7)
        @test direction_at(u_inf, 0) == FinPolySet(Int[])

        # Negative max_size is rejected.
        @test_throws ErrorException list_polynomial(max_size=-1)
    end

    # ----------------------------------------------------------
    # #2 is_linear(::Bicomodule) + LinearBicomodule (validate-and-wrap)
    # ----------------------------------------------------------
    @testset "is_linear(::Bicomodule) / LinearBicomodule" begin
        # Discrete comonoid → regular_bicomodule has carrier `linear(S)`,
        # i.e. every position has direction-set of size 1. Linear.
        cd = discrete_comonoid(FinPolySet([:a, :b]))
        Bd = regular_bicomodule(cd)
        @test is_linear(Bd)
        L = LinearBicomodule(Bd)
        @test L.underlying === Bd

        # State-system comonoid carrier is Sy^S — direction-set at each
        # position has cardinality |S| > 1 for |S| > 1. Not linear.
        S = FinPolySet([:s, :t])
        cs = state_system_comonoid(S)
        Bns = regular_bicomodule(cs)
        @test !is_linear(Bns)
        @test_throws ErrorException LinearBicomodule(Bns)

        # Singleton state-system: |S|=1 makes Sy^S = y, which is linear.
        c1 = state_system_comonoid(FinPolySet([:only]))
        @test is_linear(regular_bicomodule(c1))
    end

    # ----------------------------------------------------------
    # #3 linear_bicomodule_from_span — Cor 6.17 (forward only)
    # ----------------------------------------------------------
    @testset "linear_bicomodule_from_span" begin
        # Discrete bases — trivial action satisfies validate_bicomodule.
        C = discrete_comonoid(FinPolySet([:c1, :c2]))
        D = discrete_comonoid(FinPolySet([:d1, :d2, :d3]))
        S = FinPolySet([:s1, :s2, :s3, :s4])

        # span: s1,s2 ↦ c1; s3,s4 ↦ c2; s1,s3 ↦ d1; s2 ↦ d2; s4 ↦ d3
        sf = x -> x in (:s1, :s2) ? :c1 : :c2
        tf = x -> x === :s1 ? :d1 :
                  x === :s2 ? :d2 :
                  x === :s3 ? :d1 : :d3

        L = linear_bicomodule_from_span(C, D, S, sf, tf)
        @test L isa LinearBicomodule
        B = L.underlying
        @test validate_bicomodule(B)
        @test positions(B.carrier) == S
        @test is_linear(B)
        @test B.left_base === C
        @test B.right_base === D

        # Validation rejects bad spans.
        @test_throws ErrorException linear_bicomodule_from_span(
            C, D, S, x -> :nope, tf)
        @test_throws ErrorException linear_bicomodule_from_span(
            C, D, S, sf, x -> :also_nope)

        # validate=false skips the boundary check; the resulting bicomodule
        # may not satisfy the bicomodule axioms (since `s` returns garbage),
        # but at least construction succeeds.
        L2 = linear_bicomodule_from_span(C, D, S, sf, tf; validate=false)
        @test L2 isa LinearBicomodule

        # Non-discrete bases: trivial-action construction succeeds (no error
        # raised), but the resulting bicomodule is NOT guaranteed to validate.
        # PolyAggregation's discrete-schema use case is the supported path in
        # v0.5.1; the v0.6 bridge_diagram machinery will give a fuller treatment.
        c_nondiscrete = free_labeled_transition_comonoid([:a, :b],
                                                          [(:a, :f, :b)])
        L3 = linear_bicomodule_from_span(c_nondiscrete, c_nondiscrete,
                                         positions(c_nondiscrete.carrier),
                                         identity, identity)
        @test L3 isa LinearBicomodule
        @test positions(L3.underlying.carrier) ==
              positions(c_nondiscrete.carrier)
    end

    # ----------------------------------------------------------
    # #4 c_one_y(c) — Theorem 8.8 carrier (left c-module packaged as a
    # c-1-bicomodule with the unit comonoid on the right)
    # ----------------------------------------------------------
    @testset "c_one_y" begin
        c = free_labeled_transition_comonoid([:a, :b], [(:a, :f, :b)])
        L = c_one_y(c)
        @test L isa LinearBicomodule
        B = L.underlying
        @test validate_bicomodule(B)
        @test is_linear(B)
        # Positions of c(1)y are exactly the objects of c.
        @test Set(positions(B.carrier).elements) == Set([:a, :b])
        @test B.left_base === c
        # Right base is the unit comonoid (one object :pt).
        @test cardinality(positions(B.right_base.carrier)) == Finite(1)

        # Left action follows c-morphism codomains: at :a, the f-arrow
        # `(:f,)` lifts to :b; the identity stays at :a.
        i, jbar = B.left_coaction.on_positions.f(:a)
        @test i == :a
        @test jbar[()] == :a
        @test jbar[(:f,)] == :b

        # Discrete comonoid: c(1)y still validates (cod-tracking collapses
        # to trivial action when every morphism is an identity).
        cd = discrete_comonoid(FinPolySet([:x, :y_, :z]))
        Ld = c_one_y(cd)
        @test Set(positions(Ld.underlying.carrier).elements) ==
              Set([:x, :y_, :z])
        @test validate_bicomodule(Ld.underlying)
    end

end  # v0.5.1
