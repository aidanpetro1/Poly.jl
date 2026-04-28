# ============================================================
# Extensions v1, PR #7: TABULATE_SIZE_CAP message + setter
# ============================================================
#
# Coverage:
#
#   1. `set_tabulate_cap!` round-trips and returns the previous value
#   2. `set_tabulate_cap!` rejects negative input
#   3. The over-cap error enumerates all four escape hatches

@testset "Extensions v1, PR #7: TABULATE_SIZE_CAP" begin

    @testset "set_tabulate_cap! round-trip + return value" begin
        original = TABULATE_SIZE_CAP[]
        try
            prev = set_tabulate_cap!(42)
            @test prev == original
            @test TABULATE_SIZE_CAP[] == 42
            prev2 = set_tabulate_cap!(original)
            @test prev2 == 42
            @test TABULATE_SIZE_CAP[] == original
        finally
            # Defensive: restore even if a test failed mid-flight.
            TABULATE_SIZE_CAP[] = original
        end
    end

    @testset "set_tabulate_cap! rejects negative input" begin
        @test_throws ArgumentError set_tabulate_cap!(-1)
    end

    @testset "over-cap error message lists all four escape hatches" begin
        original = TABULATE_SIZE_CAP[]
        try
            set_tabulate_cap!(2)
            # A function whose domain is bigger than the cap.
            big_dom = FinPolySet([:a, :b, :c, :d])
            pf = PolyFunction(big_dom, big_dom, x -> x)
            err = nothing
            try
                tabulate(pf)
            catch e
                err = e
            end
            @test err !== nothing
            msg = sprint(showerror, err)
            # Must surface the four escape hatches plus the diagnostic numbers.
            @test occursin("$(length(big_dom.elements))", msg)
            @test occursin("force = true", msg) || occursin("force=true", msg)
            @test occursin("set_tabulate_cap!", msg)
            @test occursin("structural", msg)
            @test occursin("Dict", msg)
        finally
            TABULATE_SIZE_CAP[] = original
        end
    end

end  # @testset "Extensions v1, PR #7: TABULATE_SIZE_CAP"
