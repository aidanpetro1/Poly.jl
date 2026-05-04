# ============================================================
# v0.4.x patch: validate_bicomodule_composition_detailed —
# `:compose_base_identity` is a soft note, not a hard failure
# ============================================================
#
# Spec: PolyCDS v1.7 deep-modularity follow-up (2026-05-02), follow-up
# to `subst_targeted_lens_lazy` ship.
#
# `validate_bicomodule_composition_detailed` previously pushed a
# `:compose_base_identity` `ValidationFailure` whenever
# `M.right_base !== N.left_base` even though their carriers were `==`.
# But `compose(M, N)` itself uses `==` on carriers (not `===` on the
# Comonoid), so it succeeds in this case. The validator's verdict
# (`.passed = false`) was inconsistent with the operation's semantics.
#
# The natural shape of any compositional build that constructs
# intermediate bases via independent `parallel` reductions and then
# composes hits this: tensored bases come out `==`-equal but `!==` by
# object identity, since `parallel(::Bicomodule, ::Bicomodule)` builds
# a fresh `_comonoid_carrier_tensor` afresh each call.
#
# Fix (Option A): drop the `push!(failures, f)` and early
# `return fail(...)` for that branch. Keep the diagnostic via verbose
# println so callers whose downstream code requires `===` on bases
# (e.g. `BicomoduleMorphism`) can still surface it.
#
# Tests cover:
#
#   1. The principal regression — `M.right_base !== N.left_base` with
#      `==`-equal carriers no longer causes `.passed` to be `false`,
#      and `compose(M, N)` / `compose_lazy(M, N)` actually succeed.
#   2. `:compose_base_identity` does not appear in `r.failures`.
#   3. Genuine carrier mismatch (`:compose_base_mismatch`) still fails
#      hard — the patch is targeted, not a wholesale relaxation.
#   4. Verbose mode still surfaces the diagnostic message (for
#      `BicomoduleMorphism`-style downstream consumers).

@testset "v0.4.x: :compose_base_identity is a soft note" begin

    # ------------------------------------------------------------
    # 1. Principal regression: independently-constructed comonoids
    #    on the same carrier, composed via their regular bicomodules.
    # ------------------------------------------------------------
    @testset "==-equal-but-!== bases: validator passes, compose succeeds" begin
        S = FinPolySet([:p1, :p2])
        c1 = state_system_comonoid(S)
        c2 = state_system_comonoid(S)
        # Pre-condition for this test to be meaningful:
        @test c1 !== c2
        @test c1.carrier == c2.carrier

        M = regular_bicomodule(c1)   # M.right_base === c1
        N = regular_bicomodule(c2)   # N.left_base  === c2
        @test M.right_base === c1
        @test N.left_base  === c2
        @test M.right_base !== N.left_base
        @test M.right_base.carrier == N.left_base.carrier

        # Pre-fix: r.passed was `false` because :compose_base_identity
        # was pushed to failures. Post-fix: validator's verdict tracks
        # what compose actually does.
        r = validate_bicomodule_composition_detailed(M, N)
        @test r.passed
        @test isempty(r.failures)
        @test all(f -> f.law !== :compose_base_identity, r.failures)

        # And both eager and lazy compose succeed (which they always
        # did — this is the actual semantics the validator now matches).
        composite = compose(M, N)
        @test composite isa Bicomodule
        composite_lazy = compose_lazy(M, N)
        @test composite_lazy isa Bicomodule
    end

    # ------------------------------------------------------------
    # 2. Genuine carrier mismatch still fails hard
    # ------------------------------------------------------------
    @testset "carrier mismatch (:compose_base_mismatch) still fails" begin
        # Different state set on the right side: the carriers are
        # structurally distinct, so compose(M, N) would error. The
        # validator should catch this before compose runs.
        S  = FinPolySet([:p1, :p2])
        Sʹ = FinPolySet([:q1, :q2, :q3])
        c1 = state_system_comonoid(S)
        c3 = state_system_comonoid(Sʹ)

        M = regular_bicomodule(c1)
        N = regular_bicomodule(c3)
        @test M.right_base.carrier != N.left_base.carrier

        r = validate_bicomodule_composition_detailed(M, N)
        @test !r.passed
        @test any(f -> f.law === :compose_base_mismatch, r.failures)
        # And :compose_base_identity is *still* not pushed (the carrier
        # branch fires first, and we no longer push the identity branch
        # at all).
        @test all(f -> f.law !== :compose_base_identity, r.failures)
    end

    # ------------------------------------------------------------
    # Helper: capture stdout produced by `f()` to a String. Uses
    # `mktemp` so the redirect target is a real `IOStream` (the
    # method `redirect_stdout` actually accepts — IOBuffer is not
    # supported, see the v0.4.x test errata).
    # ------------------------------------------------------------
    capture_stdout(f) = mktemp() do path, io
        try
            redirect_stdout(io) do
                f()
            end
        finally
            close(io)
        end
        read(path, String)
    end

    # ------------------------------------------------------------
    # 3. Verbose mode surfaces the soft-note diagnostic
    # ------------------------------------------------------------
    @testset "verbose=true / :all prints the cross/base-object diagnostic" begin
        S = FinPolySet([:p1, :p2])
        c1 = state_system_comonoid(S)
        c2 = state_system_comonoid(S)
        M = regular_bicomodule(c1)
        N = regular_bicomodule(c2)

        # verbose=true should print the diagnostic; verbose=false should not.
        out_verbose = capture_stdout() do
            validate_bicomodule_composition_detailed(M, N; verbose=true)
        end
        @test occursin("cross/base-object", out_verbose)
        @test occursin("compose(M, N) will succeed", out_verbose)

        # verbose=:all should also print it (and may print other stuff).
        out_all = capture_stdout() do
            validate_bicomodule_composition_detailed(M, N; verbose=:all)
        end
        @test occursin("cross/base-object", out_all)

        # Default (verbose=false) is silent for the soft note.
        out_quiet = capture_stdout() do
            validate_bicomodule_composition_detailed(M, N; verbose=false)
        end
        @test !occursin("cross/base-object", out_quiet)
    end

    # ------------------------------------------------------------
    # 4. Identical-bases case: still passes, no diagnostic
    # ------------------------------------------------------------
    @testset "M.right_base === N.left_base: clean pass, no diagnostic" begin
        S = FinPolySet([:a, :b])
        c = state_system_comonoid(S)
        M = regular_bicomodule(c)
        N = regular_bicomodule(c)   # same c, so M.right_base === N.left_base
        @test M.right_base === N.left_base

        r = validate_bicomodule_composition_detailed(M, N)
        @test r.passed
        @test isempty(r.failures)

        # No verbose noise about base-object identity in the === path.
        out = capture_stdout() do
            validate_bicomodule_composition_detailed(M, N; verbose=true)
        end
        @test !occursin("cross/base-object", out)
    end

end  # @testset "v0.4.x: :compose_base_identity is a soft note"
