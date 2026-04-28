# ============================================================
# Extensions v1, PR #4: First-class Coalgebra
# ============================================================
#
# Coverage:
#
#   1. Construction: full + Lens-inferred
#   2. Shape rejection: domain not Sy^S, codomain mismatch
#   3. Round-trip: Coalgebra → to_lens → Coalgebra
#   4. moore_machine_coalgebra convenience
#   5. CoalgebraMorphism construction + commuting-square validation
#   6. Non-commuting morphism rejection
#   7. validate_coalgebra_detailed surfaces shape failures
#   8. Bool / detailed API parity

@testset "Extensions v1, PR #4: Coalgebra" begin

    @testset "construction: full + Lens-inferred" begin
        S = FinPolySet([:s1, :s2, :s3])
        I = FinPolySet([:lo, :hi])
        A = FinPolySet([:tick])
        # Build a Moore-machine lens, then promote to Coalgebra two ways.
        φ = moore_machine(S, I, A,
                s -> s == :s1 ? :lo : :hi,
                (s, _) -> s == :s1 ? :s2 : (s == :s2 ? :s3 : :s1))
        # Inferred form
        c1 = Coalgebra(φ)
        @test c1 isa Coalgebra
        @test c1.carrier == S
        @test c1.polynomial == monomial(I, A)
        # Full form
        c2 = Coalgebra(S, monomial(I, A), φ)
        @test c2 isa Coalgebra
        @test c2.carrier == c1.carrier
        @test c2.polynomial == c1.polynomial
    end

    @testset "shape rejection: bad domain" begin
        # Lens whose dom isn't Sy^S — should be rejected by Coalgebra(::Lens).
        wrong_dom = Polynomial(FinPolySet([:p]), _ -> FinPolySet([:d1, :d2]))
        cod_p = Polynomial(FinPolySet([:q]), _ -> FinPolySet([:e]))
        bogus = Lens(wrong_dom, cod_p, _ -> :q, (_, _) -> :d1)
        @test_throws ErrorException Coalgebra(bogus)
    end

    @testset "shape rejection: codomain mismatch" begin
        S = FinPolySet([:s1, :s2])
        p = monomial(FinPolySet([:o]), FinPolySet([:a]))
        q = monomial(FinPolySet([:o]), FinPolySet([:b]))   # different polynomial
        φ = Lens(state_system(S), p, _ -> :o, (_, _) -> :s1)
        # Full constructor with a polynomial that doesn't match structure.cod
        @test_throws ErrorException Coalgebra(S, q, φ)
    end

    @testset "to_lens round-trip" begin
        S = FinPolySet([:s1, :s2])
        c = moore_machine_coalgebra(S, FinPolySet([:o]), FinPolySet([:a]),
                s -> :o, (s, _) -> s == :s1 ? :s2 : :s1)
        φ = to_lens(c)
        c2 = Coalgebra(φ)
        @test c2.carrier == c.carrier
        @test c2.polynomial == c.polynomial
        @test c2.structure == c.structure
    end

    @testset "moore_machine_coalgebra convenience" begin
        S = FinPolySet([:on, :off])
        I = FinPolySet([:bright, :dark])
        A = FinPolySet([:toggle])
        c = moore_machine_coalgebra(S, I, A,
                s -> s == :on ? :bright : :dark,
                (s, _) -> s == :on ? :off : :on)
        @test c isa Coalgebra
        @test c.carrier == S
        @test validate_coalgebra(c)
    end

    @testset "CoalgebraMorphism: identity commutes" begin
        # Build a coalgebra; its identity self-morphism must commute.
        S = FinPolySet([:s1, :s2])
        I = FinPolySet([:o])
        A = FinPolySet([:a])
        c = moore_machine_coalgebra(S, I, A, _ -> :o, (s, _) -> s == :s1 ? :s2 : :s1)
        id_map = identity_lens(state_system(S))
        f = CoalgebraMorphism(c, c, id_map)
        @test f isa CoalgebraMorphism
        @test validate_coalgebra_morphism(f)
    end

    @testset "CoalgebraMorphism: collapsing morphism commutes" begin
        # A 2-state coalgebra and a 1-state coalgebra over the same polynomial,
        # with a map that collapses both states to the single state. Must
        # commute provided both coalgebras agree on the (single) output and
        # the dynamics fold correctly.
        I = FinPolySet([:o])
        A = FinPolySet([:a])
        # 2-state: both states output :o, both step to themselves under :a.
        Sbig = FinPolySet([:s1, :s2])
        c_big = moore_machine_coalgebra(Sbig, I, A, _ -> :o, (s, _) -> s)
        # 1-state collapsing target: outputs :o, steps to itself.
        Ssmall = FinPolySet([:t])
        c_small = moore_machine_coalgebra(Ssmall, I, A, _ -> :o, (_, _) -> :t)
        # Map: both s1 and s2 collapse to t. on_directions: t's direction is :t
        # (since state_system uses S as the direction set), pulled back to the
        # corresponding state in Sbig.
        collapse = Lens(state_system(Sbig), state_system(Ssmall),
                        _ -> :t,
                        (s, _t) -> s)   # pulling back :t to s preserves dom-direction
        f = CoalgebraMorphism(c_big, c_small, collapse)
        @test validate_coalgebra_morphism(f)
    end

    @testset "CoalgebraMorphism: non-commuting rejected by validator" begin
        # Two coalgebras over the same polynomial whose dynamics disagree;
        # the identity-on-states map can't be a coalgebra morphism between
        # them.
        S = FinPolySet([:s1, :s2])
        I = FinPolySet([:lo, :hi])
        A = FinPolySet([:a])
        c1 = moore_machine_coalgebra(S, I, A,
                s -> s == :s1 ? :lo : :hi,
                (s, _) -> s == :s1 ? :s2 : :s1)
        c2 = moore_machine_coalgebra(S, I, A,
                s -> s == :s1 ? :hi : :lo,                # outputs swapped
                (s, _) -> s == :s1 ? :s2 : :s1)
        id_map = identity_lens(state_system(S))
        f = CoalgebraMorphism(c1, c2, id_map)
        # Constructor accepts (shape is fine); validator rejects.
        @test !validate_coalgebra_morphism(f)
        result = validate_coalgebra_morphism_detailed(f)
        @test !result.passed
        @test !isempty(result.failures)
        @test result.failures[1].law == :commuting_square
    end

    @testset "validate_coalgebra_detailed and Bool API parity" begin
        S = FinPolySet([:s])
        c = moore_machine_coalgebra(S, FinPolySet([:o]), FinPolySet([:a]),
                _ -> :o, (_, _) -> :s)
        @test validate_coalgebra(c) === true
        @test validate_coalgebra_detailed(c) isa ValidationResult
        @test validate_coalgebra_detailed(c).passed
    end

    @testset "Coalgebra distinct from Comodule (different concept)" begin
        # Documenting the distinction: a Coalgebra here is over an endofunctor
        # (no laws); a comodule is over a comonoid (counit + coassoc laws).
        # Both happen to wrap a `Lens` but they're structurally different
        # types with different validation semantics. This test pins the type
        # distinction in case someone later tries to unify them.
        S = FinPolySet([:s])
        c_alg = moore_machine_coalgebra(S, FinPolySet([:o]), FinPolySet([:a]),
                _ -> :o, (_, _) -> :s)
        @test c_alg isa Coalgebra
        @test !(c_alg isa Comonoid)
        @test !(c_alg isa Bicomodule)
    end

end  # @testset "Extensions v1, PR #4: Coalgebra"
