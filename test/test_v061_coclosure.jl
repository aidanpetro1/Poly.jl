# ============================================================
# v0.6.1 — coclosure + Example 5.5 + Lemma 8.7 + is_reflexive
# ============================================================
#
# After reading the FA paper (arXiv 2111.10968v7), the v0.6 stub for
# `comonoid_from_list_polynomial` is replaced with a paper-faithful
# implementation. The key insight: the comonoid lives on `[u/u]`, not
# on `u` itself. Five additive items:
#
#   1. coclosure(q, p)                         — FA Prop 2.16, Closure.jl
#   2. comonoid_from_coclosure(p)              — FA Example 5.5, Comonoid.jl
#   3. comonoid_from_list_polynomial(u_K)      — FA Lemma 8.7, Demos.jl
#   4. is_reflexive(p)                         — FA Example 7.2, Polynomial.jl
#   5. (bridge_diagram docstring update)       — FA Prop 3.20, CatSharp.jl
#
# Tests exercise the paper identities and the Fin^op truncation check.

@testset "v0.6.1: coclosure + Example 5.5 + Lemma 8.7 + is_reflexive" begin

    # ----------------------------------------------------------
    # #1 coclosure(q, p) — FA Prop 2.16
    # ----------------------------------------------------------
    @testset "coclosure" begin
        # FA Example 2.18: [Q/P] = P · y^Q for sets P, Q (constant
        # polynomials with empty direction-sets are NOT what we want;
        # the example's "set" framing uses representable y^P-style).
        # Instead test the coclosure formula directly.

        # Simple finite case: p = y^A, q = y^B.
        # [y^B / y^A] = Σ_{i ∈ y^A(1)} y^{(y^B)(y^A[i])}
        #             = Σ_{:pt} y^{(y^B)(A)}.
        # (y^B)(A) = pairs (j, g : B → A); for B finite, |y^B(A)| = |A|^|B|.
        A = FinPolySet([:a, :b])
        B = FinPolySet([:b1, :b2, :b3])
        yA = representable(A)
        yB = representable(B)

        cc = coclosure(yB, yA)
        # Positions of [y^B / y^A] = positions of y^A = {:pt}.
        @test cardinality(positions(cc)) == Finite(1)
        # Direction-set at :pt = (y^B)(A). |A|^|B| = 2^3 = 8.
        @test cardinality(direction_at(cc, :pt)) == Finite(8)

        # Pure linear case: p = Ay, q = y. [y/Ay] = Σ_{i ∈ A} y^{y(Ay[i])}.
        # Ay[i] = {:pt}, so y(Ay[i]) = y({:pt}) = pairs (:pt, Dict(:pt=>:pt)).
        # |y({:pt})| = 1.
        Ay = linear(A)
        cc2 = coclosure(y, Ay)
        @test cardinality(positions(cc2)) == Finite(2)  # |A| = 2
        for a in A.elements
            @test cardinality(direction_at(cc2, a)) == Finite(1)
        end

        # FA Prop 2.16 paper example reduces:
        # [y/y] = Σ_{i ∈ y(1)} y^{y(y[i])} = y^{y({:pt})} = y^1 = y.
        cc3 = coclosure(y, y)
        @test cc3 ≈ y

        # Refuses non-finite operands.
        @test_throws ErrorException coclosure(y, list_polynomial())
        @test_throws ErrorException coclosure(list_polynomial(), y)
    end

    # ----------------------------------------------------------
    # #2 comonoid_from_coclosure(p) — FA Example 5.5
    # ----------------------------------------------------------
    @testset "comonoid_from_coclosure" begin
        # Tiny p with non-trivial structure: p = y + y^2.
        # p(1) = {1, 2}, p[1] = {:a}, p[2] = {:b1, :b2}.
        # [p/p] has 2 positions. At position 1, direction-set = p(p[1]) =
        # p({:a}) = pairs (j, g) with j ∈ {1, 2} and g : p[j] → {:a}.
        # j=1: g : {:a} → {:a}, only one (the identity), so 1 morphism.
        # j=2: g : {:b1, :b2} → {:a}, only the constant-:a function, 1.
        # Total: 2 morphisms out of position 1.
        # At position 2, direction-set = p(p[2]) = p({:b1, :b2}).
        # j=1: g : {:a} → {:b1, :b2}, 2 functions.
        # j=2: g : {:b1, :b2} → {:b1, :b2}, 4 functions.
        # Total: 6 morphisms out of position 2.
        p = Polynomial(FinPolySet([1, 2]),
                       i -> i == 1 ? FinPolySet([:a]) :
                                     FinPolySet([:b1, :b2]))

        c = comonoid_from_coclosure(p)
        @test c isa Comonoid
        @test validate_comonoid(c)
        @test validate_comonoid(c; mode=:lens)

        # Carrier positions match p(1).
        @test Set(positions(c.carrier).elements) == Set([1, 2])

        # Morphism counts per Example 5.5.
        cat = to_category(c)
        out_1 = filter(m -> cat.dom[m] == 1, cat.morphisms.elements)
        out_2 = filter(m -> cat.dom[m] == 2, cat.morphisms.elements)
        @test length(out_1) == 2
        @test length(out_2) == 6

        # Identity at 1 is (1, id_{p[1]}) = (1, Dict(:a => :a)).
        # The morphism encoding wraps the comonoid direction (j, g) as
        # the carrier-direction; identity[1] = (1, (1, Dict(:a => :a))).
        id1 = cat.identity[1]
        @test id1[1] == 1                  # dom packing
        @test id1[2][1] == 1               # codomain in [p/p] = 1
        @test id1[2][2] == Dict(:a => :a)  # underlying map is identity

        # Codomain of (1, (j, g)) is j (the codomain in [p/p]).
        for m in cat.morphisms.elements
            i, (j, _g) = m
            @test cat.cod[m] == j
        end
    end

    # ----------------------------------------------------------
    # #3 comonoid_from_list_polynomial — FA Lemma 8.7 (Fin^op)
    # ----------------------------------------------------------
    @testset "comonoid_from_list_polynomial (Lemma 8.7)" begin
        # Truncation K = 3 → Fin^op restricted to objects {0, 1, 2, 3}.
        u_3 = list_polynomial(max_size=3)
        c_fin_op_3 = comonoid_from_list_polynomial(u_3)

        @test c_fin_op_3 isa Comonoid
        @test validate_comonoid(c_fin_op_3)

        # Positions of carrier = {0, 1, 2, 3}.
        @test Set(positions(c_fin_op_3.carrier).elements) == Set(0:3)

        # Morphism count out of N: |[u/u][N]| = |u(u[N])| = |u({1,...,N})|
        # = Σ_{j=0..3} N^j.
        cat = to_category(c_fin_op_3)
        for N in 0:3
            expected = sum(N^j for j in 0:3)
            actual = count(m -> cat.dom[m] == N, cat.morphisms.elements)
            @test actual == expected
        end

        # At N = 0, the only morphism is the identity (the empty
        # function {} → {} viewed as a 0-direction).
        out_0 = filter(m -> cat.dom[m] == 0, cat.morphisms.elements)
        @test length(out_0) == 1
        @test cat.identity[0] == out_0[1]

        # Composition matches Fin^op semantics: morphism (1, g) at N
        # composed with (1, h) at 1 gives (1, g ∘ h) at N.
        # Here g : {1} → {1,...,N} is some constant function,
        # h : {1} → {1} is the identity, g ∘ h = g.
        # Test on a specific case at N = 2.
        # Morphisms out of 2 with codomain 1: (1, g) for g : {1} → {1, 2}.
        # There are 2 such morphisms: g(1) = 1 or g(1) = 2.
        m_at_2_to_1 = filter(m -> cat.dom[m] == 2 && cat.cod[m] == 1,
                             cat.morphisms.elements)
        @test length(m_at_2_to_1) == 2

        # Refuses unbounded list_polynomial.
        @test_throws ErrorException comonoid_from_list_polynomial(list_polynomial())

        # Comonoid_from_coclosure on the same polynomial gives the same
        # comonoid (modulo == on Comonoid, which doesn't exist; check
        # carrier equality and a representative pos/dir agreement).
        c_via_alias = comonoid_from_coclosure(u_3)
        @test positions(c_via_alias.carrier) == positions(c_fin_op_3.carrier)
        for N in 0:3
            @test direction_at(c_via_alias.carrier, N) ==
                  direction_at(c_fin_op_3.carrier, N)
        end
    end

    # ----------------------------------------------------------
    # #4 is_reflexive — FA Example 7.2
    # ----------------------------------------------------------
    @testset "is_reflexive (Example 7.2)" begin
        A = FinPolySet([:a, :b, :c])

        # Representables and linears are reflexive.
        @test is_reflexive(y)
        @test is_reflexive(representable(A))
        @test is_reflexive(linear(A))

        # constant(I) for non-empty I is NOT reflexive (multiple
        # positions, multiple direction-sets that aren't all singletons).
        @test !is_reflexive(constant(A))
        # constant(∅) = zero_poly: 0 positions, vacuously linear (every
        # direction-set is singleton, since there are none). Edge case:
        # both predicates trivially true. Reflexive.
        @test is_reflexive(zero_poly)
        # one_poly: 1 position, direction-set ∅. Representable (1 pos).
        @test is_reflexive(one_poly)

        # y^A + Ay (sum of two reflexive types) is NOT reflexive
        # (multiple positions with different-sized direction-sets).
        @test !is_reflexive(representable(A) + linear(A))

        # weak_dual on the reflexive subcategory is idempotent.
        @test weak_dual(weak_dual(linear(A))) ≈ linear(A)
        @test weak_dual(weak_dual(representable(A))) ≈ representable(A)
    end

end  # v0.6.1
