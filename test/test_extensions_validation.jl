# ============================================================
# Extensions v1, PR #6: Structural validation diagnostics
# ============================================================
#
# Coverage:
#
#   1. ValidationResult Bool conversion: existing call sites work transparently
#   2. Passing comonoid produces a ValidationResult with no failures
#   3. Comonoid with broken duplicator produces failures with structural hints
#   4. minimal_failing_triple over compat failures
#   5. verbose=:all collects every failure rather than stopping at first
#   6. ValidationFailure carries actual / expected / law / structural_hint

@testset "Extensions v1, PR #6: ValidationResult" begin

    @testset "Bool API: validate_* returns Bool" begin
        S = FinPolySet([:s1, :s2])
        c = state_system_comonoid(S)
        # `validate_comonoid` returns Bool for back-compat with @test and
        # existing call sites; the rich result is exposed via the
        # `_detailed` companion.
        @test validate_comonoid(c) isa Bool
        @test validate_comonoid(c)
        # Conditional usage:
        ok = false
        if validate_comonoid(c)
            ok = true
        end
        @test ok
    end

    @testset "validate_*_detailed exposes ValidationResult" begin
        S = FinPolySet([:s1, :s2, :s3])
        c = state_system_comonoid(S)
        result = validate_comonoid_detailed(c; mode=:lens)
        @test result isa ValidationResult
        @test result.passed
        @test isempty(result.failures)

        result_cat = validate_comonoid_detailed(c; mode=:category)
        @test result_cat isa ValidationResult
        @test result_cat.passed
        @test isempty(result_cat.failures)
    end

    @testset "ValidationFailure carries structural hint, law, actual, expected" begin
        # Construct a deliberately-broken comonoid by tampering with the
        # duplicator's on_positions to violate the first-component law.
        S = FinPolySet([:s1, :s2])
        c = state_system_comonoid(S)
        # Build a broken duplicator: returns wrong first component.
        broken_dup = Lens(c.carrier, c.duplicator.cod,
                          s -> (:wrong, Dict(t => t for t in S.elements)),
                          (s, ab) -> ab[2])
        # Build a Comonoid that bypasses the constructor's `is_subst_of` check
        # by going through `Base.invokelatest` would be overkill — instead, we
        # invoke validate on the lens-form check directly.
        # Use a "fake" comonoid struct via reflection-free path: just call the
        # internal validator with a custom test. Simpler: build a comonoid with
        # the broken duplicator (constructor will fail unless the cod still
        # matches subst). The cod IS still subst(carrier, carrier) since we
        # reused c.duplicator.cod, so construction succeeds.
        broken_c = Comonoid(c.carrier, c.eraser, broken_dup)
        result = validate_comonoid_detailed(broken_c; mode=:lens)
        @test !result.passed
        @test !isempty(result.failures)

        first_failure = result.failures[1]
        @test first_failure isa ValidationFailure
        @test first_failure.law == :delta_first_component
        @test occursin("duplicator", first_failure.structural_hint)
        @test occursin("position", first_failure.structural_hint)
        @test first_failure.actual == :wrong
        # `expected` is the first state we tried.
        @test first_failure.expected in S.elements
    end

    @testset "verbose=:all collects every failure" begin
        # Same broken comonoid as above. With :all we should see *every*
        # failing position, not just the first.
        S = FinPolySet([:s1, :s2, :s3])
        c = state_system_comonoid(S)
        broken_dup = Lens(c.carrier, c.duplicator.cod,
                          s -> (:wrong, Dict(t => t for t in S.elements)),
                          (s, ab) -> ab[2])
        broken_c = Comonoid(c.carrier, c.eraser, broken_dup)

        result_first = validate_comonoid_detailed(broken_c; mode=:lens, verbose=false)
        result_all   = validate_comonoid_detailed(broken_c; mode=:lens, verbose=:all)
        # :all should produce strictly more failures than the default first-fail mode.
        @test length(result_all.failures) > length(result_first.failures)
        # All failures in :all carry the same law symbol (first-component).
        @test all(f -> f.law == :delta_first_component, result_all.failures)
    end

    @testset "minimal_failing_triple on bicomodule compat failures" begin
        # Hand-build a set of compat-failure tuples and check the helper
        # picks the lex-smallest. (We don't engineer a real failing
        # bicomodule — the helper itself is the unit under test.)
        f1 = ValidationFailure(:compatibility_positions, (:x2, :b1, :a1),
                               "hint1", :got1, :exp1)
        f2 = ValidationFailure(:compatibility_positions, (:x1, :b2, :a2),
                               "hint2", :got2, :exp2)
        f3 = ValidationFailure(:compatibility_positions, (:x1, :b1, :a3),
                               "hint3", :got3, :exp3)
        smallest = minimal_failing_triple([f1, f2, f3])
        @test smallest.location == (:x1, :b1, :a3)
    end

    @testset "validate_bicomodule_detailed returns ValidationResult" begin
        S = FinPolySet([:s1, :s2])
        c = state_system_comonoid(S)
        B = regular_bicomodule(c)
        result = validate_bicomodule_detailed(B)
        @test result isa ValidationResult
        @test result.passed
        @test isempty(result.failures)
        # Bool API still works.
        @test validate_bicomodule(B) === true
    end

    @testset "minimal_failing_triple integrates with validate_bicomodule_detailed" begin
        # On a deliberately-failing bicomodule, validate_bicomodule_detailed's
        # `.failures` should be a `Vector{ValidationFailure}` consumable by
        # `minimal_failing_triple`. We can't easily *construct* a failing
        # bicomodule from primitives without also breaking the constructor's
        # shape check (the cod must still be subst(...)), so we build a
        # tampered Lens whose on_positions and on_directions return the
        # wrong values for one specific input — preserving the cod shape
        # but breaking the right-comodule and compatibility axioms at known
        # triples. This exercises the end-to-end plumbing.
        S = FinPolySet([:s1, :s2])
        c = state_system_comonoid(S)
        carrier = c.carrier
        # Build a tampered right_coaction: on positions returns the right
        # shape, but on directions, at position :s1 with input (:s1, :s1)
        # we return :s2 instead of :s1, breaking the right counit law and
        # cascading compatibility violations.
        good_right = c.duplicator
        tampered_right = Lens(carrier, good_right.cod,
            good_right.on_positions.f,
            (s, ab) -> begin
                # Default behavior: return ab[2]. Tamper at s = :s1.
                if s == :s1 && ab == (:s1, :s1)
                    return :s2
                end
                return ab[2]
            end)
        B = Bicomodule(carrier, c, c, c.duplicator, tampered_right)
        result = validate_bicomodule_detailed(B; verbose=:all)
        @test !result.passed
        @test result.failures isa Vector{ValidationFailure}
        @test !isempty(result.failures)

        # Each failure's location is a Tuple; minimal_failing_triple expects
        # 3-tuples. Filter and pass.
        triples = filter(f -> length(f.location) == 3, result.failures)
        @test !isempty(triples)
        smallest = minimal_failing_triple(triples)
        @test smallest isa ValidationFailure
        @test length(smallest.location) == 3
        # The smallest triple should have x = :s1 (lex-smallest carrier
        # position involved in the tampered region).
        @test smallest.location[1] == :s1
    end

    @testset "ValidationResult printing is informative" begin
        # The text/plain show method should include "passed" or "FAILED".
        passing = ValidationResult(true)
        @test occursin("passed", sprint(show, MIME"text/plain"(), passing))

        failing = ValidationResult(false,
            [ValidationFailure(:law_x, (:obj,), "broken at obj", 1, 2)],
            "test summary")
        text = sprint(show, MIME"text/plain"(), failing)
        @test occursin("FAILED", text)
        @test occursin("law_x", text)
        @test occursin("broken at obj", text)
        @test occursin("test summary", text)
    end

end  # @testset "Extensions v1, PR #6: ValidationResult"
