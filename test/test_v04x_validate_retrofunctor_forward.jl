# ============================================================
# v0.5 patch: forward-action-aware `validate_retrofunctor` for
# partial-image retrofunctors
# ============================================================
#
# Spec: PolyCDS v1.7 iso test continuation, 2026-05-02. Companion to
# the v0.4.x forward-action patch on `base_change_left` /
# `base_change_right` — same architectural seam, different consumer
# surface (self-validation rather than Cat# operations).
#
# Tests cover:
#
#   1. Partial-image retrofunctor (tuple of cofree-morphisms over
#      alphabet-inclusion lenses) — the back-action-based validator
#      errors via the `tuple_retrofunctor` agreement check; the
#      forward-action validator passes.
#   2. Total-back-action retrofunctor (identity) — the forward
#      validator passes; the strict back-action validator continues to
#      pass unchanged (regression-only check).
#   3. Error surface — forward validator errors when called on a
#      retrofunctor with `forward_on_directions === nothing`.
#   4. `_detailed` companion returns a `ValidationResult` whose
#      `.passed` matches the bool-returning function.
#   5. Verbose modes — `verbose=true` and `verbose=:all` work without
#      throwing.

@testset "v0.5 validate_retrofunctor_forward" begin

    # ------------------------------------------------------------
    # 1. Partial-image retrofunctor: tuple of cofree-morphisms over
    #    alphabet-inclusion lenses (PolyCDS-style boundary).
    #
    #    The back-action `validate_retrofunctor(f; strict=true)` reaches
    #    `compose(F.dom.duplicator, subst(F.underlying, F.underlying))`
    #    and probes `tuple_retrofunctor`'s on-directions on tensored
    #    direction tuples like `((), (:c,))` — components disagree by
    #    design on non-image tuples, and the agreement check errors.
    #    The forward-action validator never touches `on_directions` and
    #    succeeds.
    # ------------------------------------------------------------
    @testset "partial-image tuple_retrofunctor: forward passes, strict errors" begin
        Σ_full = FinPolySet([:a, :b, :c])
        Σ_d1   = FinPolySet([:a, :b])
        Σ_d2   = FinPolySet([:a, :c])
        depth  = 1

        # Alphabet-inclusion lenses: each `L_d : y^Σ_full → y^Σ_d` has
        # `pos: pt → pt`, `dir: σ_d ↦ σ_d` (inclusion Σ_d ↪ Σ_full).
        L1 = Lens(representable(Σ_full), representable(Σ_d1),
                  _ -> :pt, (_, σ) -> σ)
        L2 = Lens(representable(Σ_full), representable(Σ_d2),
                  _ -> :pt, (_, σ) -> σ)
        F1 = cofree_morphism(L1, depth)
        F2 = cofree_morphism(L2, depth)
        boundary = tuple_retrofunctor([F1, F2])

        # Sanity: forward action populated by both sub-constructors.
        @test boundary.forward_on_directions !== nothing

        # Strict back-action validation errors via the tuple_retrofunctor
        # agreement check at a non-image tensored direction.
        @test_throws Exception validate_retrofunctor(boundary; strict=true)

        # Element-wise back-action validation hits the same wall (it
        # also calls `F.underlying.on_directions.f(i).f(...)` on every
        # cod-direction at every position).
        @test_throws Exception validate_retrofunctor(boundary; strict=false)

        # Forward-action validation succeeds — the boundary satisfies
        # counit + the composition law (forward respects path
        # concatenation in cofree comonoids), which is the invariant
        # this validator checks. NOT the strict comonoid-morphism
        # axioms (which the boundary doesn't satisfy in general); see
        # docs/dev/forward_action.md for the position-side carve-out.
        @test validate_retrofunctor_forward(boundary)
    end

    # ------------------------------------------------------------
    # 1b. cofree_morphism alone over alphabet inclusion at depth ≥ 2 —
    #     exercises non-trivial composition where the filter actually
    #     drops directions in the middle of a path.
    # ------------------------------------------------------------
    @testset "cofree_morphism over alphabet inclusion: depth-2 composition" begin
        Σ_full = FinPolySet([:a, :b, :c])
        Σ_d1   = FinPolySet([:a, :b])    # drops :c
        L1 = Lens(representable(Σ_full), representable(Σ_d1),
                  _ -> :pt, (_, σ) -> σ)
        F = cofree_morphism(L1, 2)

        # cofree_morphism over a non-identity L is a strict back-action
        # retrofunctor (per its docstring). Forward validation passes
        # too — the composition law holds because filter-subsequence
        # respects path concatenation. (Position-side comult would
        # fail here on directions outside L's image, e.g. (:c,) — but
        # that's not a check this validator does.)
        @test validate_retrofunctor(F; strict=true)
        @test validate_retrofunctor_forward(F)
    end

    # ------------------------------------------------------------
    # 2. Total-back-action retrofunctor (identity): forward and strict
    #    validators agree.
    # ------------------------------------------------------------
    @testset "identity_retrofunctor: forward and strict both pass" begin
        cs = state_system_comonoid(FinPolySet([:s1, :s2, :s3]))
        F = identity_retrofunctor(cs)

        # Both modes pass on the identity. Forward is the substantive
        # new check; strict is a regression sanity check that the
        # existing path still works.
        @test validate_retrofunctor_forward(F)
        @test validate_retrofunctor(F; strict=true)
        @test validate_retrofunctor(F; strict=false)
    end

    # ------------------------------------------------------------
    # 3. Forward validator errors with no forward_on_directions.
    # ------------------------------------------------------------
    @testset "forward validator requires forward_on_directions" begin
        cs = state_system_comonoid(FinPolySet([:a, :b]))
        # Construct a Retrofunctor without the forward kwarg.
        F = Retrofunctor(cs, cs, identity_lens(cs.carrier))
        @test F.forward_on_directions === nothing
        @test_throws ErrorException validate_retrofunctor_forward(F)
        # And `*_detailed` errors equivalently before returning a result.
        @test_throws ErrorException validate_retrofunctor_forward_detailed(F)
    end

    # ------------------------------------------------------------
    # 4. `_detailed` companion mirrors the bool function.
    # ------------------------------------------------------------
    @testset "validate_retrofunctor_forward_detailed: ValidationResult shape" begin
        cs = state_system_comonoid(FinPolySet([:s1, :s2]))
        F = identity_retrofunctor(cs)

        r = validate_retrofunctor_forward_detailed(F)
        @test r isa ValidationResult
        @test r.passed === true
        @test isempty(r.failures)

        # And on the partial-image case: forward-detailed also passes,
        # and the result is a ValidationResult not a thrown exception.
        Σ_full = FinPolySet([:a, :b, :c])
        Σ_d1   = FinPolySet([:a, :b])
        Σ_d2   = FinPolySet([:a, :c])
        L1 = Lens(representable(Σ_full), representable(Σ_d1),
                  _ -> :pt, (_, σ) -> σ)
        L2 = Lens(representable(Σ_full), representable(Σ_d2),
                  _ -> :pt, (_, σ) -> σ)
        boundary = tuple_retrofunctor([cofree_morphism(L1, 1),
                                       cofree_morphism(L2, 1)])
        r2 = validate_retrofunctor_forward_detailed(boundary)
        @test r2 isa ValidationResult
        @test r2.passed === true
    end

    # ------------------------------------------------------------
    # 5. Verbose modes do not throw.
    # ------------------------------------------------------------
    @testset "verbose=true and verbose=:all on a passing retrofunctor" begin
        cs = state_system_comonoid(FinPolySet([:s1, :s2]))
        F = identity_retrofunctor(cs)
        # Capture stdout to keep test output clean. Both verbose modes
        # should return true on this passing retrofunctor and not error.
        mktemp() do _path, io
            redirect_stdout(io) do
                @test validate_retrofunctor_forward(F; verbose=true)
                @test validate_retrofunctor_forward(F; verbose=:all)
            end
        end
    end

end  # @testset "v0.5 validate_retrofunctor_forward"
