# ============================================================
# Extensions v2, PR #6: back_directions / BackDirectionTable / sharp_L / sharp_R
# ============================================================
#
# Lens.on_directions is opaque without a wrapper. `back_directions`
# materializes it as a `BackDirectionTable` for inspection — keys are
# `(pos, codir)` pairs, values are the corresponding domain directions.
# `materialize` modes: `:auto` (default, cap-aware), `true` (force or
# error if over cap), `false` (always callable). `sharp_L` / `sharp_R`
# are Bicomodule shorthands.

@testset "Extensions v2, PR #6: back_directions / sharp_L / sharp_R" begin

    @testset "back_directions on identity lens — happy path" begin
        # id_p has on_directions(i) = identity on p[i]; the materialized
        # table's entry at (i, b) is b for every b in p[i].
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        id_p = identity_lens(p)
        t = back_directions(id_p)
        @test t isa BackDirectionTable
        @test length(t) == 3  # (i1, a), (i1, b), (i2, c)
        @test t[(:i1, :a)] == :a
        @test t[(:i1, :b)] == :b
        @test t[(:i2, :c)] == :c
        # 2-arg getindex
        @test t[:i1, :a] == :a
    end

    @testset "back_directions on a non-trivial lens" begin
        # Coin-jar / owner lens flavor (similar to Sprint 2 example).
        q = Polynomial(FinPolySet([:open, :closed]),
                       i -> i == :open ? FinPolySet([:penny, :nickel]) :
                                          FinPolySet(Symbol[]))
        p = Polynomial(FinPolySet([:m]),
                       i -> FinPolySet([:save, :spend]))
        f = Lens(p, q, i -> :open, (i, b) -> b == :penny ? :spend : :save)
        t = back_directions(f)
        @test t isa BackDirectionTable
        @test length(t) == 2  # (m, penny), (m, nickel)
        @test t[(:m, :penny)] == :spend
        @test t[(:m, :nickel)] == :save
    end

    @testset "materialize=false always returns callable" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        id_p = identity_lens(p)
        c = back_directions(id_p; materialize=false)
        @test c isa Function
        @test c(:i, :a) == :a
    end

    @testset "materialize=true on small lens — succeeds" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        id_p = identity_lens(p)
        t = back_directions(id_p; materialize=true)
        @test t isa BackDirectionTable
    end

    @testset "auto mode falls back to callable when over cap" begin
        # Build a lens with > TABULATE_SIZE_CAP entries by temporarily
        # lowering the cap. The cap restoration is via try/finally so
        # other tests are unaffected.
        old_cap = Poly.set_tabulate_cap!(2)
        try
            p = Polynomial(FinPolySet([:i1, :i2, :i3]),
                           _ -> FinPolySet([:a, :b]))
            id_p = identity_lens(p)
            # Total entries = 6 > cap of 2 — :auto returns callable.
            r = back_directions(id_p; materialize=:auto)
            @test r isa Function
            @test r(:i1, :a) == :a
        finally
            Poly.set_tabulate_cap!(old_cap)
        end
    end

    @testset "materialize=true over cap errors with helpful message" begin
        old_cap = Poly.set_tabulate_cap!(2)
        try
            p = Polynomial(FinPolySet([:i1, :i2, :i3]),
                           _ -> FinPolySet([:a, :b]))
            id_p = identity_lens(p)
            err = nothing
            try
                back_directions(id_p; materialize=true)
            catch e
                err = e
            end
            @test err isa ErrorException
            @test occursin("TABULATE_SIZE_CAP", err.msg)
            @test occursin("set_tabulate_cap!", err.msg)
        finally
            Poly.set_tabulate_cap!(old_cap)
        end
    end

    @testset "BackDirectionTable: pairs / iteration / haskey" begin
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        id_p = identity_lens(p)
        t = back_directions(id_p)

        @test haskey(t, (:i1, :a))
        @test !haskey(t, (:i1, :z))

        # Iterate via pairs.
        all_pairs = collect(pairs(t))
        @test length(all_pairs) == 3
    end

    @testset "BackDirectionTable: pretty show is multi-line" begin
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        id_p = identity_lens(p)
        t = back_directions(id_p)

        # One-line show
        s_inline = sprint(show, t)
        @test occursin("BackDirectionTable", s_inline)
        @test occursin("3 entries", s_inline)

        # Multi-line REPL show
        s_pretty = sprint(show, MIME"text/plain"(), t)
        @test occursin("↦", s_pretty)
        @test count(c -> c == '\n', s_pretty) >= 2  # at least one position group
    end

    @testset "sharp_L / sharp_R on regular bicomodule" begin
        S = FinPolySet([:a, :b, :c])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        tL = sharp_L(B)
        tR = sharp_R(B)
        @test tL isa BackDirectionTable
        @test tR isa BackDirectionTable
        # The regular bicomodule's coactions are the duplicator on both
        # sides; back-directions should non-trivially populate.
        @test length(tL) > 0
        @test length(tR) > 0
    end

    @testset "sharp_L / sharp_R respect materialize keyword" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        @test sharp_L(B; materialize=false) isa Function
        @test sharp_R(B; materialize=false) isa Function
    end

    # ============================================================
    # Adversarial tests
    # ============================================================

    @testset "adversarial — empty domain lens" begin
        # Lens whose domain has zero positions: no entries at all.
        p_empty = Polynomial(FinPolySet(Symbol[]), _ -> FinPolySet(Symbol[]))
        id_empty = identity_lens(p_empty)
        t = back_directions(id_empty)
        @test t isa BackDirectionTable
        @test length(t) == 0
    end

    @testset "adversarial — domain position with empty cod direction-set" begin
        # If on_positions(i) lands at a cod-position with empty
        # direction-set, that position contributes 0 entries (not 1).
        p = Polynomial(FinPolySet([:lone]), _ -> FinPolySet(Symbol[]))
        q = Polynomial(FinPolySet([:lone]), _ -> FinPolySet(Symbol[]))
        f = Lens(p, q, _ -> :lone, (_, _) -> error("vacuous"))
        t = back_directions(f)
        @test length(t) == 0
    end

    @testset "adversarial — :auto on empty lens still returns table" begin
        # Empty lens: total = 0 ≤ cap, so :auto materializes.
        p_empty = Polynomial(FinPolySet(Symbol[]), _ -> FinPolySet(Symbol[]))
        id_empty = identity_lens(p_empty)
        @test back_directions(id_empty; materialize=:auto) isa BackDirectionTable
    end

    @testset "adversarial — equality of identically-shaped tables" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        id_p = identity_lens(p)
        @test back_directions(id_p) == back_directions(id_p)
    end

    @testset "adversarial — invalid materialize value errors" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        id_p = identity_lens(p)
        @test_throws ArgumentError back_directions(id_p; materialize=:nope)
    end

    @testset "adversarial — non-finite domain cannot materialize" begin
        # NatSet domain — back_directions cannot enumerate; :auto and
        # false return callable, true errors.
        p_nat = Polynomial(NatSet(),
                           _ -> FinPolySet([:a]))
        # Construct identity-like lens manually; can't use identity_lens
        # because that requires iteration.
        on_pos = PolyFunction(NatSet(), NatSet(), identity)
        on_dir = DependentFunction(
            NatSet(),
            i -> ExpSet(FinPolySet([:a]), FinPolySet([:a])),
            i -> PolyFunction(FinPolySet([:a]), FinPolySet([:a]), identity)
        )
        f_nat = Lens(p_nat, p_nat, on_pos, on_dir)

        @test back_directions(f_nat; materialize=:auto) isa Function
        @test back_directions(f_nat; materialize=false) isa Function
        @test_throws ArgumentError back_directions(f_nat; materialize=true)
    end

    @testset "adversarial — table independent of cap fluctuations" begin
        # Materialize with a generous cap, then DROP the cap below the
        # entry count. Existing table object is unaffected.
        p = Polynomial(FinPolySet([:i1, :i2]),
                       _ -> FinPolySet([:a, :b]))
        id_p = identity_lens(p)
        t = back_directions(id_p; materialize=true)
        @test length(t) == 4

        old = Poly.set_tabulate_cap!(1)
        try
            @test t[(:i1, :a)] == :a   # still works post-cap-change
        finally
            Poly.set_tabulate_cap!(old)
        end
    end

    @testset "adversarial — sharp_L on a known-broken bicomodule still tabulates" begin
        # Even when validate_bicomodule fails, sharp_L should still
        # materialize the back-directions of the (technically wrong)
        # left coaction. The user's debugging path: get the table,
        # eyeball it, find the error.
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        bogus_left = Lens(cs.carrier, subst(cs.carrier, cs.carrier),
                          _ -> (:a, Dict(t => t for t in S.elements)),
                          (_, ab) -> ab[2])
        B = Bicomodule(cs.carrier, cs, cs, bogus_left, cs.duplicator)
        @test !validate_bicomodule(B)
        # Despite invalid coaction, sharp_L still produces a table.
        @test sharp_L(B) isa BackDirectionTable
    end

end
