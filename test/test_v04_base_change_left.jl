# ============================================================
# v0.4.x #5: base_change_left(F::Retrofunctor, M::Bicomodule)
# ============================================================
#
# Driven by PolyCDS deep-modularity refactor (2026-05-02 ask): given
# F : C₀ → C and M : C ⇸ D, restrict M's left base from C to C₀ along F.
#
# Coverage:
#
#   1. Identity F preserves M element-wise.
#   2. Shape check: F.cod.carrier ≠ M.left_base.carrier errors.
#   3. Validates when inputs validate (identity F on a regular bicomodule).
#   4. Functoriality: base_change_left(compose(F,G), M) ≅
#      base_change_left(F, base_change_left(G, M)) element-wise.
#   5. Errors clearly when F is non-injective on positions.

@testset "v0.4.x #5: base_change_left" begin

    @testset "identity F preserves M element-wise" begin
        C = state_system_comonoid(FinPolySet([:c1, :c2]))
        M = regular_bicomodule(C)   # M : C ⇸ C
        idF = identity_retrofunctor(C)
        Mp = base_change_left(idF, M)

        @test Mp isa Bicomodule
        @test Mp.left_base === M.left_base
        @test Mp.right_base === M.right_base
        @test Mp.carrier === M.carrier
        # Right coaction: identical (we pass M.right_coaction through).
        @test Mp.right_coaction === M.right_coaction
        # Left coaction: element-wise equal on positions and directions.
        for x in M.carrier.positions.elements
            cp_orig, mbar_orig = M.left_coaction.on_positions.f(x)
            cp_new,  mbar_new  = Mp.left_coaction.on_positions.f(x)
            @test cp_orig == cp_new
            @test mbar_orig == mbar_new
        end
        @test validate_bicomodule(Mp)
    end

    @testset "shape check: F.cod ≠ M.left_base errors" begin
        C = state_system_comonoid(FinPolySet([:c1, :c2]))
        D = state_system_comonoid(FinPolySet([:d1, :d2]))
        M = regular_bicomodule(C)
        wrong_F = identity_retrofunctor(D)   # F.cod = D, not C
        @test_throws ErrorException base_change_left(wrong_F, M)
    end

    @testset "validates when inputs validate (identity F)" begin
        C = state_system_comonoid(FinPolySet([:s1, :s2, :s3]))
        M = regular_bicomodule(C)
        idF = identity_retrofunctor(C)
        Mp = base_change_left(idF, M)
        @test validate_retrofunctor(idF)
        @test validate_bicomodule(M)
        @test validate_bicomodule(Mp)
    end

    @testset "functoriality on identity composition" begin
        # F : C → C, G : C → C — both identity. F ∘ G is identity.
        # base_change_left(F∘G, M) and base_change_left(F, base_change_left(G, M))
        # should agree element-wise.
        C = state_system_comonoid(FinPolySet([:s1, :s2]))
        M = regular_bicomodule(C)
        F = identity_retrofunctor(C)
        G = identity_retrofunctor(C)
        FG = compose(F, G)

        Mp_combined = base_change_left(FG, M)
        Mp_step     = base_change_left(F, base_change_left(G, M))

        @test Mp_combined.left_base === Mp_step.left_base
        @test Mp_combined.right_base === Mp_step.right_base
        @test Mp_combined.carrier === Mp_step.carrier
        for x in M.carrier.positions.elements
            cp1, mb1 = Mp_combined.left_coaction.on_positions.f(x)
            cp2, mb2 = Mp_step.left_coaction.on_positions.f(x)
            @test cp1 == cp2
            @test mb1 == mb2
        end
    end

    @testset "non-injective F on positions errors" begin
        # Build F : C₀ → C where F.on_positions sends two distinct C₀-positions
        # to the same C-position. base_change_left should refuse.
        C  = state_system_comonoid(FinPolySet([:s]))           # 1 position
        C0 = state_system_comonoid(FinPolySet([:a, :b]))       # 2 positions
        # We need a Retrofunctor C₀ → C. The lens C₀.carrier → C.carrier:
        # on_positions: both :a and :b map to :s. on_directions has to
        # respect the comonoid morphism axioms... for state_system, both
        # carriers are |X|y^|X|. Direction at :s in C is {:s}. We map both
        # :a and :b's direction-set ({:a, :b}) backward — F.on_directions
        # at :a sends C-dir :s ↦ C₀-dir :a; at :b sends :s ↦ :b. (This
        # is a valid lens but not necessarily a valid retrofunctor; the
        # construction is enough to trigger base_change_left's
        # non-injectivity error.)
        bad_lens = Lens(
            C0.carrier, C.carrier,
            _ -> :s,                    # both positions → :s
            (i, _) -> i                 # back-action: identity-ish
        )
        bad_F = Retrofunctor(C0, C, bad_lens)

        M = regular_bicomodule(C)
        @test_throws ErrorException base_change_left(bad_F, M)
    end
end
