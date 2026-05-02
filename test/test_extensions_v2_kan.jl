# ============================================================
# Extensions v2, PR #3: Kan extensions of bicomodules
# ============================================================
#
# Per docs/dev/kan_extensions_construction.md. v0.3 ships:
#   - KanExtension struct + factor_through
#   - kan_along_bicomodule(D, M; direction=:left) — finite case
#   - kan_2cat(D, F; direction=:left) — identity-D case
#   - Σ_D / Π_D unicode aliases
#   - :right and non-identity-D :left error with clear messages (v0.3.x)

@testset "Extensions v2, PR #3: Kan extensions" begin

    # ============================================================
    # KanExtension construction + display
    # ============================================================

    @testset "kan_along_bicomodule returns a KanExtension" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        M = regular_bicomodule(cs)
        D = regular_bicomodule(cs)   # identity bicomodule on cs
        k = kan_along_bicomodule(D, M; direction=:left)
        @test k isa KanExtension
        @test k.direction === :left
        @test k.source === D
        @test k.input === M
        @test k.extension isa Bicomodule
        @test k.unit isa BicomoduleMorphism
    end

    @testset "kan_2cat returns a KanExtension on the identity case" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        D = regular_bicomodule(cs)   # identity
        F = regular_bicomodule(cs)
        k = kan_2cat(D, F; direction=:left)
        @test k isa KanExtension
        # Identity D: extension === F.
        @test k.extension === F
        @test validate_bicomodule_morphism(k.unit)  # identity 2-cell validates
    end

    @testset "KanExtension show is informative" begin
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        D = regular_bicomodule(cs)
        F = regular_bicomodule(cs)
        k = kan_2cat(D, F; direction=:left)
        s = sprint(show, k)
        @test occursin("KanExtension", s)
        @test occursin(":left", s)
    end

    # ============================================================
    # factor_through (universal property, identity case)
    # ============================================================

    @testset "factor_through on identity Kan recovers α" begin
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        D = regular_bicomodule(cs)
        F = regular_bicomodule(cs)
        k = kan_2cat(D, F; direction=:left)

        # Identity 2-cell on F.
        α = identity_bicomodule_morphism(F)
        # In the identity-D case, the factoring 2-cell IS α.
        β = factor_through(k, α)
        @test β isa BicomoduleMorphism
        @test β.source === α.source
        @test β.target === α.target
    end

    # ============================================================
    # Direction-name validation
    # ============================================================

    @testset "kan_along_bicomodule rejects bogus direction" begin
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        M = regular_bicomodule(cs)
        D = regular_bicomodule(cs)
        @test_throws ArgumentError kan_along_bicomodule(D, M; direction=:diagonal)
    end

    @testset "kan_2cat rejects bogus direction" begin
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        D = regular_bicomodule(cs)
        F = regular_bicomodule(cs)
        @test_throws ArgumentError kan_2cat(D, F; direction=:diagonal)
    end

    # ============================================================
    # Not-yet-implemented paths error with clear messages
    # ============================================================

    @testset ":right Kan with identity D works (v0.3.1)" begin
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        M = regular_bicomodule(cs)
        D = regular_bicomodule(cs)
        # As of v0.3.1, right-Kan ships for identity D and finite
        # non-identity D. The identity case returns M unchanged with
        # an identity counit.
        k = kan_along_bicomodule(D, M; direction=:right)
        @test k isa KanExtension
        @test k.direction === :right
        @test k.extension === M
    end

    @testset "kan_2cat non-identity D errors with clear message" begin
        # Build a non-identity bicomodule by tensoring two regular ones.
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        M_reg = regular_bicomodule(cs)
        D_nontrivial = parallel(M_reg, M_reg)   # a non-identity bicomodule
        # F still over cs to satisfy left_base === requirement.
        F = regular_bicomodule(cs)
        # kan_2cat requires D.left_base === F.left_base; this won't hold
        # because tensoring built a different left_base. Test errors at
        # that check, OR at the non-identity check — either way it's
        # a clean error path.
        err = nothing
        try
            kan_2cat(D_nontrivial, F; direction=:left)
        catch e
            err = e
        end
        @test err isa ErrorException
    end

    # ============================================================
    # Base-mismatch errors
    # ============================================================

    @testset "kan_along_bicomodule rejects mismatched bases" begin
        S = FinPolySet([:a])
        T = FinPolySet([:x])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)
        M = regular_bicomodule(cs)   # right_base = cs
        D_bad = regular_bicomodule(ct) # left_base = ct, mismatched
        @test_throws ErrorException kan_along_bicomodule(D_bad, M; direction=:left)
    end

    @testset "kan_2cat rejects mismatched left_base" begin
        S = FinPolySet([:a])
        T = FinPolySet([:x])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)
        D = regular_bicomodule(cs)
        F = regular_bicomodule(ct)
        @test_throws ErrorException kan_2cat(D, F; direction=:left)
    end

    # ============================================================
    # Unicode aliases
    # ============================================================

    @testset "Σ_D unicode alias works" begin
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        M = regular_bicomodule(cs)
        D = regular_bicomodule(cs)
        k1 = kan_along_bicomodule(D, M; direction=:left)
        k2 = Poly.var"Σ_D"(D, M)
        @test k2 isa KanExtension
        @test k2.direction === :left
        @test k1.extension.carrier == k2.extension.carrier
    end

    @testset "Π_D unicode alias works (right Kan, identity D, v0.3.1)" begin
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        M = regular_bicomodule(cs)
        D = regular_bicomodule(cs)
        k = Poly.var"Π_D"(D, M)
        @test k isa KanExtension
        @test k.direction === :right
        @test k.extension === M    # identity D: Π_D M ≅ M
    end

    # ============================================================
    # Adversarial tests
    # ============================================================

    @testset "adversarial — KanExtension constructor rejects bogus direction" begin
        # Direct struct construction with bad symbol should error.
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        F = regular_bicomodule(cs)
        unit = identity_bicomodule_morphism(F)
        @test_throws ArgumentError KanExtension(F, unit, :diagonal, F, F)
    end

    @testset "adversarial — factor_through on non-identity D errors" begin
        # Same setup as identity case, but lie about the source by
        # passing a non-identity-shaped Kan.
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        M = regular_bicomodule(cs)
        D = regular_bicomodule(cs)   # identity for kan_along — but compose gives non-trivial extension
        k = kan_along_bicomodule(D, M; direction=:left)
        # k's source IS the regular bicomodule (identity-shaped). For
        # kan_along with identity D, the extension IS bigger than M, so
        # factor_through requires α.source.carrier == k.extension.carrier.
        # Pass a non-matching α; expect an error.
        α_bad = identity_bicomodule_morphism(M)   # α.source.carrier = M.carrier ≠ extension.carrier
        @test_throws ErrorException factor_through(k, α_bad)
    end

    @testset "adversarial — kan_2cat on smallest case (singleton)" begin
        S = FinPolySet([:lone])
        cs = state_system_comonoid(S)
        D = regular_bicomodule(cs)
        F = regular_bicomodule(cs)
        k = kan_2cat(D, F; direction=:left)
        @test k.extension === F
        @test validate_bicomodule_morphism(k.unit)
    end

    @testset "adversarial — KanExtension type parameter is recoverable" begin
        # The extension's concrete type should be preserved in T.
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        D = regular_bicomodule(cs)
        F = regular_bicomodule(cs)
        k = kan_2cat(D, F; direction=:left)
        @test typeof(k).parameters[1] === Bicomodule
    end

end
