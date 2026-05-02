# ============================================================
# Extensions v2, PR #2: BicomoduleMorphism + horizontal composition
# ============================================================
#
# A 2-cell α : M ⇒ N between two bicomodules sharing left and right
# bases. Underlying = a polynomial Lens M.carrier → N.carrier respecting
# both coactions. Companion API: identity_bicomodule_morphism, vertical
# composition, validation (Bool + detailed), whiskering, full horizontal
# composition.

@testset "Extensions v2, PR #2: BicomoduleMorphism + horizontal compose" begin

    # ============================================================
    # Construction + identity + validation
    # ============================================================

    @testset "identity_bicomodule_morphism validates" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        α = identity_bicomodule_morphism(B)
        @test α isa BicomoduleMorphism
        @test α.source === B
        @test α.target === B
        @test validate_bicomodule_morphism(α)
    end

    @testset "constructor enforces base identity (Q2.1)" begin
        # Two regular bicomodules over the same comonoid object => OK.
        # Build two SEPARATE comonoid objects with the same data and
        # confirm the identity check rejects them.
        S = FinPolySet([:a, :b])
        cs1 = state_system_comonoid(S)
        cs2 = state_system_comonoid(S)
        B1 = regular_bicomodule(cs1)
        B2 = regular_bicomodule(cs2)
        # cs1 !== cs2 (separate objects), so source.left_base !== target.left_base.
        @test cs1 !== cs2
        underlying = identity_lens(B1.carrier)
        @test_throws ErrorException BicomoduleMorphism(B1, B2, underlying)
    end

    @testset "constructor enforces underlying lens shape" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        # Lens with wrong domain.
        wrong_dom = Polynomial(FinPolySet([:x]), _ -> FinPolySet([:y]))
        wrong = Lens(wrong_dom, B.carrier,
                     _ -> first(B.carrier.positions.elements),
                     (_, _b) -> :a)
        @test_throws ErrorException BicomoduleMorphism(B, B, wrong)
    end

    # ============================================================
    # Vertical composition
    # ============================================================

    @testset "vertical compose: identity ; identity = identity" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        α = identity_bicomodule_morphism(B)
        αα = compose(α, α)
        @test αα isa BicomoduleMorphism
        @test validate_bicomodule_morphism(αα)
    end

    @testset "vertical compose: source/target mismatch errors" begin
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        α = identity_bicomodule_morphism(B)

        T = FinPolySet([:x])
        ct = state_system_comonoid(T)
        Bt = regular_bicomodule(ct)
        β = identity_bicomodule_morphism(Bt)
        @test_throws ErrorException compose(α, β)
    end

    # ============================================================
    # Validation: detailed + structured failures
    # ============================================================

    @testset "validate_bicomodule_morphism_detailed returns ValidationResult" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        α = identity_bicomodule_morphism(B)
        r = validate_bicomodule_morphism_detailed(α)
        @test r isa ValidationResult
        @test r.passed
        @test isempty(r.failures)
    end

    @testset "broken morphism: detailed surfaces a failure" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        # Build a broken underlying lens: routes :a position to :b on the
        # target side, breaking the left-coaction square.
        broken = Lens(B.carrier, B.carrier,
                      i -> i == :a ? :b : :a,         # swap positions
                      (_, b) -> b)                     # passthrough on directions
        α_broken = BicomoduleMorphism(B, B, broken)
        r = validate_bicomodule_morphism_detailed(α_broken; verbose=:all)
        @test !r.passed
        @test !isempty(r.failures)
        # At least one failure is on left or right coaction.
        @test all(f.law in (:morphism_left_positions, :morphism_left_directions,
                            :morphism_right_positions, :morphism_right_directions)
                  for f in r.failures)
    end

    # ============================================================
    # Horizontal composition / whiskering
    # ============================================================

    @testset "whisker_left: id_M whiskered with N gives id-shape morphism" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        M = regular_bicomodule(cs)
        N = regular_bicomodule(cs)
        α = identity_bicomodule_morphism(M)
        wl = whisker_left(α, N)
        @test wl isa BicomoduleMorphism
        @test wl.source.carrier == compose(M, N).carrier
        @test wl.target.carrier == compose(M, N).carrier
    end

    @testset "whisker_right: id_M whiskered with id_N over D" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        M = regular_bicomodule(cs)
        N = regular_bicomodule(cs)
        β = identity_bicomodule_morphism(N)
        wr = whisker_right(M, β)
        @test wr isa BicomoduleMorphism
    end

    @testset "horizontal_compose: id ⊙_h id" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        M = regular_bicomodule(cs)
        N = regular_bicomodule(cs)
        α = identity_bicomodule_morphism(M)
        β = identity_bicomodule_morphism(N)
        h = horizontal_compose(α, β)
        @test h isa BicomoduleMorphism
    end

    @testset "whisker_left rejects mismatched bases" begin
        S = FinPolySet([:a])
        T = FinPolySet([:x])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)
        M = regular_bicomodule(cs)   # over (cs, cs)
        N_bad = regular_bicomodule(ct)  # over (ct, ct), so M.right_base !== N_bad.left_base
        α = identity_bicomodule_morphism(M)
        @test_throws ErrorException whisker_left(α, N_bad)
    end

    # ============================================================
    # Adversarial tests
    # ============================================================

    @testset "adversarial — single-position bicomodule has identity 2-cell" begin
        S = FinPolySet([:lone])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        α = identity_bicomodule_morphism(B)
        @test validate_bicomodule_morphism(α)
    end

    @testset "adversarial — minimal_failing_triple-style lookup on morphism failures" begin
        # Failures from validate_bicomodule_morphism_detailed should be
        # uniformly shaped — the same `ValidationFailure` records that
        # validate_bicomodule produces. Confirm structure for downstream
        # tooling.
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        broken = Lens(B.carrier, B.carrier, i -> i == :a ? :b : :a, (_, b) -> b)
        α_broken = BicomoduleMorphism(B, B, broken)
        r = validate_bicomodule_morphism_detailed(α_broken; verbose=:all)
        @test !r.passed
        for f in r.failures
            @test f isa ValidationFailure
            @test f.law isa Symbol
            @test f.location isa Tuple
            @test f.structural_hint isa String
        end
    end

    @testset "adversarial — vertical composition with three 2-cells" begin
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        α = identity_bicomodule_morphism(B)
        # α ; α ; α — three-fold associative vertical compose.
        αα   = compose(α, α)
        αααA = compose(αα, α)
        αααB = compose(α, αα)
        @test validate_bicomodule_morphism(αααA)
        @test validate_bicomodule_morphism(αααB)
    end

    @testset "adversarial — manually-fused whiskers fail vertical-compose's === check" begin
        # Whiskering α and β separately and then trying to vertically
        # compose them fails because each whisker_*(*, *) call builds a
        # fresh intermediate `compose(M', N)` bicomodule, and the
        # vertical compose's `α.target === β.source` check rejects two
        # structurally-equal-but-not-identical objects. This is by
        # design: identity matching is cheap and unambiguous; users who
        # want the full horizontal composite should call
        # `horizontal_compose` (which builds the carriers exactly once).
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        M = regular_bicomodule(cs)
        N = regular_bicomodule(cs)
        α = identity_bicomodule_morphism(M)
        β = identity_bicomodule_morphism(N)

        # The fused path always works.
        @test horizontal_compose(α, β) isa BicomoduleMorphism

        # The manual whisker-then-compose path errors:
        wl = whisker_left(α, β.source)
        wr = whisker_right(α.target, β)
        @test_throws ErrorException compose(wl, wr)
    end

    @testset "adversarial — show output sane" begin
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        α = identity_bicomodule_morphism(B)
        s = sprint(show, α)
        @test occursin("BicomoduleMorphism", s)
        @test occursin("⇒", s)
    end

end
