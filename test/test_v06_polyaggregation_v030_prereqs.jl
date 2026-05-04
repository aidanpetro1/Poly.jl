# ============================================================
# v0.6 — PolyAggregation v0.3.0 prereqs
# ============================================================
#
# Four additive items per the v0.6 PR ask (filed 2026-05-04):
#
#   #1. bridge_diagram(::Bicomodule)              — src/CatSharp.jl
#   #2. weak_dual(p::AbstractPolynomial)          — src/Monoidal.jl
#   #3. comonoid_from_list_polynomial(u)          — src/Demos.jl  (stub)
#   #4. span_from_linear_bicomodule(L)            — src/CatSharp.jl
#
# Tests exercise the public surface of each item, the round-trip between
# #4 and v0.5.1's `linear_bicomodule_from_span`, and the structural
# identities flagged in the ask. PolyAggregation v0.3.0's own integration
# is exercised in PolyAggregation's test suite, not here.

@testset "v0.6: PolyAggregation v0.3.0 prereqs" begin

    # ----------------------------------------------------------
    # #4 span_from_linear_bicomodule — Cor 6.17 reverse direction
    # ----------------------------------------------------------
    @testset "span_from_linear_bicomodule" begin
        # --- Round-trip with linear_bicomodule_from_span (discrete) ---
        C = discrete_comonoid(FinPolySet([:c1, :c2]))
        D = discrete_comonoid(FinPolySet([:d1, :d2, :d3]))
        S = FinPolySet([:s1, :s2, :s3, :s4])
        sf = x -> x in (:s1, :s2) ? :c1 : :c2
        tf = x -> x === :s1 ? :d1 :
                  x === :s2 ? :d2 :
                  x === :s3 ? :d1 : :d3

        L = linear_bicomodule_from_span(C, D, S, sf, tf)
        sp = span_from_linear_bicomodule(L)

        @test sp.C === C
        @test sp.D === D
        @test sp.S == S
        # s, t recovered element-wise.
        for x in S.elements
            @test sp.s(x) == sf(x)
            @test sp.t(x) == tf(x)
        end

        # --- Special case: c_one_y(c) returns the c-1 packaging ---
        c = free_labeled_transition_comonoid([:a, :b], [(:a, :f, :b)])
        Lc = c_one_y(c)
        sp_c = span_from_linear_bicomodule(Lc)

        @test sp_c.C === c
        # Right base of c_one_y is the unit comonoid.
        @test cardinality(positions(sp_c.D.carrier)) == Finite(1)
        @test :pt in positions(sp_c.D.carrier).elements
        # S = positions of c.carrier.
        @test sp_c.S == positions(c.carrier)
        # s is identity on objects of c (cod-tracking left action's
        # first component is the input position).
        for o in positions(c.carrier).elements
            @test sp_c.s(o) == o
        end
        # t is constant :pt (the unit comonoid's single object).
        for o in positions(c.carrier).elements
            @test sp_c.t(o) == :pt
        end

        # --- Discrete comonoid round-trip via c_one_y ---
        cd = discrete_comonoid(FinPolySet([:x, :y_, :z]))
        Ld = c_one_y(cd)
        sp_d = span_from_linear_bicomodule(Ld)
        @test sp_d.S == positions(cd.carrier)
        for o in (:x, :y_, :z)
            @test sp_d.s(o) == o
            @test sp_d.t(o) == :pt
        end

        # --- Out-of-domain x raises ---
        @test_throws ErrorException sp.s(:not_in_S)
        @test_throws ErrorException sp.t(:not_in_S)
    end

    # ----------------------------------------------------------
    # #1 bridge_diagram(::Bicomodule) — Prop 3.20
    # ----------------------------------------------------------
    @testset "bridge_diagram" begin
        # --- Linear bicomodule: bridge recovers the span ---
        C = discrete_comonoid(FinPolySet([:c1, :c2]))
        D = discrete_comonoid(FinPolySet([:d1, :d2]))
        S = FinPolySet([:s1, :s2, :s3])
        sf = x -> x === :s1 ? :c1 : :c2
        tf = x -> x === :s3 ? :d2 : :d1

        L = linear_bicomodule_from_span(C, D, S, sf, tf)
        bd = bridge_diagram(L.underlying)

        # left_lens : carrier → C.carrier
        @test bd.left_lens.dom === L.underlying.carrier
        @test bd.left_lens.cod === C.carrier
        # left_lens.on_pos recovers s.
        for x in S.elements
            @test bd.left_lens.on_positions.f(x) == sf(x)
        end

        # right_lens : carrier → D.carrier
        @test bd.right_lens.dom === L.underlying.carrier
        @test bd.right_lens.cod === D.carrier
        # right_lens.on_pos recovers t.
        for x in S.elements
            @test bd.right_lens.on_positions.f(x) == tf(x)
        end

        # --- Discrete regular_bicomodule: bridge recovers obvious projections ---
        cd = discrete_comonoid(FinPolySet([:a, :b, :c]))
        Bd = regular_bicomodule(cd)
        bdd = bridge_diagram(Bd)
        # Carrier = cd.carrier = linear({:a,:b,:c}); both projections are
        # identity on positions.
        for o in (:a, :b, :c)
            @test bdd.left_lens.on_positions.f(o) == o
            @test bdd.right_lens.on_positions.f(o) == o
        end

        # --- c_one_y(c): bridge has left_lens identity-on-positions and
        # right_lens projecting to the unit comonoid's single object ---
        c = free_labeled_transition_comonoid([:p, :q], [(:p, :g, :q)])
        Lc = c_one_y(c)
        bdc = bridge_diagram(Lc.underlying)
        for o in (:p, :q)
            @test bdc.left_lens.on_positions.f(o) == o
            @test bdc.right_lens.on_positions.f(o) == :pt
        end
        @test bdc.left_lens.cod === c.carrier
        @test bdc.right_lens.cod === Lc.underlying.right_base.carrier

        # --- on_directions exercises the canonical-b lookup ---
        # For a discrete carrier, every direction is :pt.
        @test bdd.left_lens.on_directions.f(:a).f(:pt) == :pt
        @test bdd.right_lens.on_directions.f(:b).f(:pt) == :pt

        # --- bridge_diagram on regular_bicomodule(cd) and round-trip
        # consistency: left_lens.on_pos agrees with span.s element-wise.
        # cd is discrete, so regular_bicomodule(cd) is linear, and bridge
        # data should match span_from_linear_bicomodule on its
        # LinearBicomodule wrap.
        Lcd = LinearBicomodule(Bd)
        spcd = span_from_linear_bicomodule(Lcd)
        for o in spcd.S.elements
            @test bdd.left_lens.on_positions.f(o) == spcd.s(o)
            @test bdd.right_lens.on_positions.f(o) == spcd.t(o)
        end
    end

    # ----------------------------------------------------------
    # #2 weak_dual — single-variable Dirichlet [p, y]
    # ----------------------------------------------------------
    @testset "weak_dual" begin
        # weak_dual(y) ≈ y. internal_hom(y, y) has 1 lens (identity), and
        # 1 direction at that position.
        wd_y = weak_dual(y)
        @test wd_y ≈ y
        @test cardinality(positions(wd_y)) == Finite(1)

        # Niu/Spivak Example 4.81: [Iy, y] ≈ y^I and [y^I, y] ≈ Iy.
        A = FinPolySet([:a, :b, :c])
        yA = representable(A)
        Ay = linear(A)

        @test weak_dual(yA) ≈ Ay
        @test weak_dual(Ay) ≈ yA

        # Idempotence on the reflexive subcategory generated by y, y^A, Ay.
        @test weak_dual(weak_dual(y))  ≈ y
        @test weak_dual(weak_dual(yA)) ≈ yA
        @test weak_dual(weak_dual(Ay)) ≈ Ay

        # Aliasing: weak_dual(p) is definitionally internal_hom(p, y).
        @test weak_dual(yA) == internal_hom(yA, y)
        @test weak_dual(Ay) == internal_hom(Ay, y)

        # constant(I) sits OUTSIDE the reflexive subcategory: there is no
        # lens constant(I) → y, so weak_dual(constant(I)) ≈ zero_poly
        # (1 vacuous lens for I = ∅; 0 lenses otherwise).
        @test weak_dual(constant(FinPolySet(Symbol[]))) ≈ one_poly  # I = ∅: 1 lens
        wd_c = weak_dual(constant(FinPolySet([:i1, :i2])))
        @test cardinality(positions(wd_c)) == Finite(0)             # I ≠ ∅: 0 lenses

        # Closure adjunction sanity: weak_dual respects internal_hom.
        @test weak_dual(parallel(yA, Ay)) ≈ internal_hom(parallel(yA, Ay), y)
    end

    # ----------------------------------------------------------
    # #3 comonoid_from_list_polynomial — symbol existence
    # ----------------------------------------------------------
    # The full Lemma 8.7 / Fin^op semantics are exercised by the v0.6.1
    # testset (`test_v061_coclosure.jl`); here we just confirm the
    # symbol resolves so PolyAggregation v0.3.0's `using Poly:
    # comonoid_from_list_polynomial` doesn't break, and that the v0.6
    # stub-error contract has been replaced (calling on a finite
    # truncation now succeeds rather than erroring).
    @testset "comonoid_from_list_polynomial (symbol exists; v0.6.1 implements)" begin
        @test isdefined(Poly, :comonoid_from_list_polynomial)
        # v0.6.1 replaces the stub: a finite truncation now constructs
        # successfully. (See test_v061_coclosure.jl for full Lemma 8.7
        # behavioral checks.)
        u_2 = list_polynomial(max_size=2)
        @test comonoid_from_list_polynomial(u_2) isa Comonoid
        # Unbounded list_polynomial still errors clearly (v0.7 lifts).
        @test_throws ErrorException comonoid_from_list_polynomial(list_polynomial())
    end

end  # v0.6
