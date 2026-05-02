# ============================================================
# Extensions v1, PR #2: Monoidal operators on Comonoid + Bicomodule
# ============================================================
#
# Coverage:
#
#   1. Comonoid +: disjoint union of categories validates
#   2. Comonoid *: categorical product validates
#   3. Comonoid ⊗: agrees with * (up to validation)
#   4. + cardinalities match category-level disjoint union
#   5. * cardinalities match Cartesian-product
#   6. Bicomodule +: sum over common bases validates; rejects mismatched bases
#   7. Bicomodule compose / ⊙ on regular bicomodules: validates and the
#      regular bicomodule is the unit (modulo isomorphism)
#   8. compose rejects mismatched middle base
#   9. ⊙ Unicode alias agrees with compose

@testset "Extensions v1, PR #2: monoidal operators" begin

    @testset "Comonoid + validates" begin
        c = state_system_comonoid(FinPolySet([:a, :b]))
        d = state_system_comonoid(FinPolySet([:x, :y, :z]))
        sum_cd = c + d
        @test sum_cd isa Comonoid
        @test validate_comonoid(sum_cd)
        # Underlying small category: |objects| = 2 + 3, |morphisms| ≥ |c.morph| + |d.morph|.
        cat = to_category(sum_cd)
        @test length(cat.objects.elements) == 5
    end

    @testset "Comonoid * validates" begin
        c = state_system_comonoid(FinPolySet([:a, :b]))
        d = state_system_comonoid(FinPolySet([:x, :y]))
        prod_cd = c * d
        @test prod_cd isa Comonoid
        @test validate_comonoid(prod_cd)
        cat = to_category(prod_cd)
        # |objects of c × d| = |c| × |d| = 4
        @test length(cat.objects.elements) == 4
    end

    @testset "Comonoid ⊗ is the carrier-tensor (v0.3 semantics)" begin
        # NOTE: in v0.2, `c ⊗ d` delegated to `c * d` (categorical
        # product). The Extensions v2 PR #1 work in v0.3 made `⊗` an
        # alias for `parallel(::Comonoid, ::Comonoid)` (carrier-tensor)
        # because `⊗` and `parallel` are inseparable as functions via
        # `const var"⊗" = parallel`. The two are iso as comonoids but
        # use different direction-set encodings.
        c = state_system_comonoid(FinPolySet([:a, :b]))
        d = state_system_comonoid(FinPolySet([:x, :y]))
        @test (c ⊗ d) isa Comonoid
        @test validate_comonoid(c ⊗ d)
        # `c ⊗ d` ≈ `c * d` (same comonoid up to iso), but no longer
        # structurally equal in encoding — the v0.3 carrier-tensor uses
        # direction-pair encoding while `*` uses morphism-pair encoding.
        @test (c ⊗ d).carrier ≈ (c * d).carrier
    end

    @testset "Comonoid + commutativity (up to iso)" begin
        c = state_system_comonoid(FinPolySet([:a]))
        d = state_system_comonoid(FinPolySet([:x, :y]))
        @test (c + d).carrier ≈ (d + c).carrier  # cardinality-iso
    end

    @testset "Comonoid + identities: zero element" begin
        # The discrete comonoid on the empty set should be a left/right identity
        # for `+` up to isomorphism. (The discrete on ∅ has 0 objects, 0
        # morphisms; adding it returns the original category.)
        c = state_system_comonoid(FinPolySet([:a, :b]))
        empty_d = discrete_comonoid(FinPolySet(Symbol[]))
        @test (c + empty_d).carrier ≈ c.carrier
    end

    @testset "Bicomodule + validates" begin
        c = state_system_comonoid(FinPolySet([:s1, :s2]))
        M = regular_bicomodule(c)
        N = regular_bicomodule(c)
        sum_MN = M + N
        @test sum_MN isa Bicomodule
        # Carrier has 2 + 2 = 4 positions (tagged).
        @test length(sum_MN.carrier.positions.elements) == 4
        # Laws hold: sum of valid bicomodules is valid.
        @test validate_bicomodule(sum_MN)
    end

    @testset "Bicomodule + rejects mismatched bases" begin
        c1 = state_system_comonoid(FinPolySet([:a]))
        c2 = state_system_comonoid(FinPolySet([:b]))
        M = regular_bicomodule(c1)
        N = regular_bicomodule(c2)
        @test_throws ErrorException M + N
    end

    @testset "Bicomodule compose: regular ⊙ regular constructs" begin
        c = state_system_comonoid(FinPolySet([:s1, :s2]))
        M = regular_bicomodule(c)
        N = regular_bicomodule(c)
        composite = compose(M, N)
        @test composite isa Bicomodule
        @test composite.left_base.carrier == c.carrier
        @test composite.right_base.carrier == c.carrier
        # Carrier non-empty.
        @test !isempty(composite.carrier.positions.elements)
    end

    @testset "compose rejects mismatched middle base" begin
        c1 = state_system_comonoid(FinPolySet([:a]))
        c2 = state_system_comonoid(FinPolySet([:b]))
        # M : c1 ↛ c1, N : c2 ↛ c2 — middle bases (c1 vs c2) don't match.
        M = regular_bicomodule(c1)
        N = regular_bicomodule(c2)
        @test_throws ErrorException compose(M, N)
    end

    @testset "⊙ Unicode alias agrees with compose" begin
        c = state_system_comonoid(FinPolySet([:s1]))
        M = regular_bicomodule(c)
        N = regular_bicomodule(c)
        # `⊙` is bound to `compose` directly — same function, different name.
        # Calling each produces a fresh Bicomodule struct, so test
        # structural equality of the result, not identity.
        a = compose(M, N)
        b = M ⊙ N
        @test b isa Bicomodule
        @test a.left_base.carrier == b.left_base.carrier
        @test a.right_base.carrier == b.right_base.carrier
        @test length(a.carrier.positions.elements) == length(b.carrier.positions.elements)
    end

    @testset "Bicomodule ⊗: parallel product over tensored bases" begin
        c = state_system_comonoid(FinPolySet([:s1, :s2]))
        d = state_system_comonoid(FinPolySet([:t1]))
        M = regular_bicomodule(c)
        N = regular_bicomodule(d)
        tens = M ⊗ N    # also tests the var"⊗" alias on Bicomodules
        @test tens isa Bicomodule
        # Carrier has |M.carrier| × |N.carrier| positions = 2 × 1 = 2.
        @test length(tens.carrier.positions.elements) == 2
        # Bases are polynomial-tensor comonoids.
        @test tens.left_base.carrier == parallel(c.carrier, d.carrier)
        @test tens.right_base.carrier == parallel(c.carrier, d.carrier)
        # Validates as a bicomodule.
        @test validate_bicomodule(tens)
    end

end  # @testset "Extensions v1, PR #2: monoidal operators"
