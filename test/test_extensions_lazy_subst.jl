# ============================================================
# Extensions v1, PR #1: Lazy / shape-only `subst`
# ============================================================
#
# Coverage:
#
#   1. Type hierarchy: AbstractPolynomial, ConcretePolynomial, Polynomial alias
#   2. LazySubst polynomial interface
#   3. SubstPolySet cardinality (no enumeration)
#   4. materialize round-trip
#   5. subst_lazy and lazy composition (stays lazy)
#   6. is_subst_of: positive cases, fast-fail negatives, force_enumerate
#   7. Comonoid / RightComodule / LeftComodule / Bicomodule construction
#      no longer triggers eager subst enumeration

@testset "Extensions v1, PR #1: lazy subst" begin

    # ============================================================
    # 1. Type hierarchy
    # ============================================================
    @testset "type hierarchy" begin
        @test Polynomial === ConcretePolynomial
        @test ConcretePolynomial <: AbstractPolynomial
        @test LazySubst <: AbstractPolynomial
        # Existing constructors still produce concrete polynomials.
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        @test p isa ConcretePolynomial
        @test p isa AbstractPolynomial
        @test typeof(p) === Polynomial   # alias collapses
        # `y`, `zero_poly`, `one_poly` still resolve via the alias.
        @test y isa Polynomial
        @test zero_poly isa Polynomial
        @test one_poly isa Polynomial
    end

    # ============================================================
    # 2. LazySubst polynomial interface
    # ============================================================
    @testset "LazySubst interface" begin
        # Tiny p, q: p has 2 positions with 2 and 1 directions; q has 2 positions
        # with 1 and 2 directions. subst(p, q).positions = 2^2 + 2^1 = 6.
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:x]) : FinPolySet([:y, :z]))

        ls = subst_lazy(p, q)
        @test ls isa LazySubst
        @test ls.p === p
        @test ls.q === q

        # positions returns a SubstPolySet, not enumerated.
        sps = positions(ls)
        @test sps isa Poly.SubstPolySet
        # Cardinality matches the eager form.
        eager = subst(p, q)
        @test cardinality(sps) == cardinality(positions(eager))
        @test cardinality(sps) == Finite(6)   # 2^2 + 2^1

        # direction_at picks the right tagged-pair encoding.
        sample = first(positions(eager).elements)
        @test direction_at(ls, sample) == direction_at(eager, sample)
    end

    # ============================================================
    # 3. SubstPolySet cardinality
    # ============================================================
    @testset "SubstPolySet cardinality without enumeration" begin
        # Fresh polynomial with larger fan-out — eager enumeration would be
        # 5^3 + 5^2 = 150 positions, fine but exercises the formula.
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b, :c]) : FinPolySet([:d, :e]))
        q = Polynomial(FinPolySet([:j1, :j2, :j3, :j4, :j5]),
                       j -> FinPolySet([:x]))

        ls = subst_lazy(p, q)
        sps = positions(ls)
        @test cardinality(sps) == Finite(5^3 + 5^2)
        # Must agree with what the eager form would say.
        @test cardinality(sps) == cardinality(positions(subst(p, q)))
    end

    # ============================================================
    # 4. materialize round-trip
    # ============================================================
    @testset "materialize round-trip" begin
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:x]) : FinPolySet([:y, :z]))

        ls = subst_lazy(p, q)
        @test materialize(ls) == subst(p, q)

        # Idempotent on concrete.
        @test materialize(p) === p
    end

    # ============================================================
    # 5. subst_lazy / lazy composition
    # ============================================================
    @testset "lazy composition stays lazy" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        q = Polynomial(FinPolySet([:j]), _ -> FinPolySet([:b]))
        r = Polynomial(FinPolySet([:k]), _ -> FinPolySet([:c]))

        ls1 = subst_lazy(p, q)
        ls2 = subst_lazy(ls1, r)

        @test ls2 isa LazySubst
        @test ls2.p isa LazySubst       # left operand stays lazy
        @test ls2.p === ls1
        @test ls2.q === r

        # Materialize matches the eager equivalent.
        eager = subst(subst(p, q), r)
        @test materialize(ls2) == eager
    end

    # ============================================================
    # 6. is_subst_of correctness
    # ============================================================
    @testset "is_subst_of: positive cases" begin
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:x]) : FinPolySet([:y, :z]))

        # Concrete subst output recognized.
        @test is_subst_of(subst(p, q), p, q)

        # Lazy subst output: short-circuit returns true via structural equality.
        @test is_subst_of(subst_lazy(p, q), p, q)

        # Lazy with structurally-equal-but-not-identical p / q — still recognized.
        p2 = Polynomial(FinPolySet([:i1, :i2]),
                        i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q2 = Polynomial(FinPolySet([:j1, :j2]),
                        j -> j == :j1 ? FinPolySet([:x]) : FinPolySet([:y, :z]))
        @test is_subst_of(subst_lazy(p2, q2), p, q)
    end

    @testset "is_subst_of: cardinality fast-fail" begin
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:x]) : FinPolySet([:y, :z]))

        # A polynomial with the wrong number of positions for subst(p, q).
        wrong_card = Polynomial(FinPolySet([:bogus]), _ -> FinPolySet([:single]))
        @test !is_subst_of(wrong_card, p, q)

        # Empty target with non-empty expected — false.
        empty_p = Polynomial(FinPolySet(Symbol[]), _ -> FinPolySet(Symbol[]))
        @test !is_subst_of(empty_p, p, q)
        # Empty expected matches empty target.
        empty_q = empty_p
        @test is_subst_of(empty_p, empty_p, empty_p)   # subst(0, 0) ≅ 0
    end

    @testset "is_subst_of: shape fast-fail" begin
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:x]) : FinPolySet([:y, :z]))

        # Polynomial with the right cardinality but wrong tag shape: positions
        # are bare symbols, not (i, j̄) tuples.
        eager = subst(p, q)
        nposes = length(positions(eager).elements)
        bogus_pos = FinPolySet([Symbol("p$k") for k in 1:nposes])
        bogus = Polynomial(bogus_pos, _ -> FinPolySet([:any]))
        @test !is_subst_of(bogus, p, q)
    end

    @testset "is_subst_of: force_enumerate path" begin
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:x]) : FinPolySet([:y, :z]))

        # Strict equality check — should still be true.
        @test is_subst_of(subst(p, q), p, q; force_enumerate=true)
        # And false for a wrong-cardinality target even under force_enumerate.
        wrong = Polynomial(FinPolySet([:bogus]), _ -> FinPolySet([:single]))
        @test !is_subst_of(wrong, p, q; force_enumerate=true)
    end

    # ============================================================
    # 7. Constructor unblocking — comodules and bicomodule no longer
    # eagerly enumerate subst() during type-check.
    # ============================================================
    @testset "Comonoid construction validates via is_subst_of" begin
        # Pre-existing comonoid constructions should still validate:
        S = FinPolySet([:s1, :s2, :s3])
        c = state_system_comonoid(S)
        @test c isa Comonoid
        @test validate_comonoid(c)

        d = discrete_comonoid(S)
        @test d isa Comonoid
        @test validate_comonoid(d)
    end

    @testset "RightComodule / LeftComodule construction unchanged" begin
        S = FinPolySet([:s1, :s2, :s3])
        c = state_system_comonoid(S)

        rm = regular_right_comodule(c)
        @test rm isa RightComodule
        @test validate_right_comodule(rm)

        lm = regular_left_comodule(c)
        @test lm isa LeftComodule
        @test validate_left_comodule(lm)
    end

    @testset "Bicomodule construction unchanged" begin
        S = FinPolySet([:s1, :s2, :s3])
        c = state_system_comonoid(S)

        B = regular_bicomodule(c)
        @test B isa Bicomodule
        @test validate_bicomodule(B)
    end

    # ============================================================
    # 8. Smoke test for the unblocker at moderate scale
    # ============================================================
    @testset "moderate-scale Bicomodule construction" begin
        # state_system on a 4-element set: subst(Sy^S, Sy^S) has 4 * 4^4 = 1024
        # positions. Validates is_subst_of's cardinality path on a non-trivial
        # case without bloating CI runtime.
        S = FinPolySet([:s1, :s2, :s3, :s4])
        c = state_system_comonoid(S)
        B = regular_bicomodule(c)
        @test B isa Bicomodule
        @test validate_bicomodule(B)
    end

    @testset "reviewer-scale Bicomodule construction (5-state state-system)" begin
        # Reviewer's pathological case: state-system with 5 states (each
        # position has 5 directions). subst(Sy^S, Sy^S) eagerly enumerates
        # 5 * 5^5 = 15625 positions × up to 25 directions each. Under the
        # old `==`-against-`subst(...)` constructor check this was the
        # regression that motivated PR #1. With `is_subst_of` it's a
        # cardinality + sample check.
        #
        # We don't programmatically assert "fast" (timing tests are flaky),
        # but the test must complete without OOM and validation must pass.
        S = FinPolySet([:s1, :s2, :s3, :s4, :s5])
        c = state_system_comonoid(S)
        B = regular_bicomodule(c)
        @test B isa Bicomodule
        @test validate_bicomodule(B)
    end

    @testset "is_subst_of: more negative cases" begin
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:x]) : FinPolySet([:y, :z]))

        # Lazy target with mismatched lazy operands: short-circuit returns false.
        wrong_p = Polynomial(FinPolySet([:other]), _ -> FinPolySet([:d]))
        @test !is_subst_of(subst_lazy(wrong_p, q), p, q)

        # Right-cardinality target but first position is not a tuple.
        eager = subst(p, q)
        nposes = length(positions(eager).elements)
        bare_pos = FinPolySet([Symbol("p$k") for k in 1:nposes])
        bare_target = Polynomial(bare_pos, _ -> FinPolySet([:any]))
        @test !is_subst_of(bare_target, p, q)

        # Right-cardinality target with (Int, _) tuples but jbar isn't a Dict.
        # This exercises the `jbar isa AbstractDict || return false` branch.
        bogus_jbar_elts = [(:i1, :not_a_dict) for _ in 1:nposes]
        bogus_jbar = FinPolySet(bogus_jbar_elts)
        bogus_target = Polynomial(bogus_jbar, _ -> FinPolySet([:any]))
        @test !is_subst_of(bogus_target, p, q)
    end

end  # @testset "Extensions v1, PR #1: lazy subst"
