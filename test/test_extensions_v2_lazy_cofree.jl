# ============================================================
# Extensions v2, PR #8: Lazy cofree comonoid
# ============================================================
#
# Per Q8.1 (multi-select all four ops), Q8.2 (tree_at), Q8.3 (cache +
# clear_cache!). LazyCofreeComonoid defers eager `behavior_trees`
# enumeration until first access; result cached.

@testset "Extensions v2, PR #8: LazyCofreeComonoid" begin

    # ============================================================
    # Construction + lazy state
    # ============================================================

    @testset "cofree_lazy returns an unmaterialized lazy cofree" begin
        p = Polynomial(FinPolySet([:run, :halt]),
                       i -> i == :run ? FinPolySet([:tick]) : FinPolySet(Symbol[]))
        c = cofree_lazy(p, 2)
        @test c isa LazyCofreeComonoid
        @test !is_materialized(c)
        @test c.p === p
        @test c.depth == 2
    end

    @testset "show indicates lazy/materialized state" begin
        p = Polynomial(FinPolySet([:run]), _ -> FinPolySet([:tick]))
        c = cofree_lazy(p, 1)
        s_lazy = sprint(show, c)
        @test occursin("lazy", s_lazy)
        materialize(c)
        s_mat = sprint(show, c)
        @test occursin("materialized", s_mat)
    end

    @testset "cofree_lazy rejects negative depth" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        @test_throws ArgumentError cofree_lazy(p, -1)
    end

    # ============================================================
    # Operations that DON'T materialize (Q8.1)
    # ============================================================

    @testset "validate_comonoid does not force materialization" begin
        p = Polynomial(FinPolySet([:run, :halt]),
                       i -> i == :run ? FinPolySet([:tick]) : FinPolySet(Symbol[]))
        c = cofree_lazy(p, 2)
        @test validate_comonoid(c)        # default: structural answer
        @test !is_materialized(c)         # confirm no materialization
    end

    @testset "validate_comonoid(force=true) materializes and runs full validator" begin
        p = Polynomial(FinPolySet([:run, :halt]),
                       i -> i == :run ? FinPolySet([:tick]) : FinPolySet(Symbol[]))
        c = cofree_lazy(p, 2)
        @test validate_comonoid(c; force=true)
        @test is_materialized(c)          # forced
    end

    @testset "structural equality compares (p, depth) without materializing" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        c1 = cofree_lazy(p, 2)
        c2 = cofree_lazy(p, 2)
        c3 = cofree_lazy(p, 3)
        @test c1 == c2
        @test c1 != c3
        @test !is_materialized(c1)
        @test !is_materialized(c2)
    end

    # ============================================================
    # Materialization + cache (Q8.3)
    # ============================================================

    @testset "materialize forces enumeration and caches" begin
        p = Polynomial(FinPolySet([:run, :halt]),
                       i -> i == :run ? FinPolySet([:tick]) : FinPolySet(Symbol[]))
        c = cofree_lazy(p, 2)
        @test !is_materialized(c)
        eager1 = materialize(c)
        @test is_materialized(c)
        @test eager1 isa Comonoid
        # Second call hits the cache — same Comonoid object identity.
        eager2 = materialize(c)
        @test eager1 === eager2
    end

    @testset "clear_cache! frees the cache" begin
        p = Polynomial(FinPolySet([:run]), _ -> FinPolySet([:tick]))
        c = cofree_lazy(p, 1)
        materialize(c)
        @test is_materialized(c)
        clear_cache!(c)
        @test !is_materialized(c)
        # Re-materialize: new Comonoid object.
        eager_new = materialize(c)
        @test eager_new isa Comonoid
    end

    @testset "cofree_lazy materialized result agrees with cofree_comonoid" begin
        p = Polynomial(FinPolySet([:run, :halt]),
                       i -> i == :run ? FinPolySet([:tick]) : FinPolySet(Symbol[]))
        for d in 0:2
            lazy_eager = materialize(cofree_lazy(p, d))
            eager = cofree_comonoid(p, d)
            @test cardinality(lazy_eager.carrier.positions) ==
                  cardinality(eager.carrier.positions)
            @test Set(lazy_eager.carrier.positions.elements) ==
                  Set(eager.carrier.positions.elements)
        end
    end

    # ============================================================
    # eraser / duplicator forwarders
    # ============================================================

    @testset "eraser(::LazyCofreeComonoid) returns a Lens" begin
        p = Polynomial(FinPolySet([:run]), _ -> FinPolySet([:tick]))
        c = cofree_lazy(p, 1)
        e = eraser(c)
        @test e isa Lens
        @test e.cod == y
    end

    @testset "duplicator(::LazyCofreeComonoid) returns a Lens" begin
        p = Polynomial(FinPolySet([:run]), _ -> FinPolySet([:tick]))
        c = cofree_lazy(p, 1)
        d = duplicator(c)
        @test d isa Lens
    end

    # ============================================================
    # tree_at (Q8.2)
    # ============================================================

    @testset "tree_at returns the i-th tree" begin
        p = Polynomial(FinPolySet([:run, :halt]),
                       i -> i == :run ? FinPolySet([:tick]) : FinPolySet(Symbol[]))
        c = cofree_lazy(p, 1)
        t = tree_at(c, 1)
        @test t isa BehaviorTree
    end

    @testset "tree_at out of bounds errors" begin
        p = Polynomial(FinPolySet([:run]), _ -> FinPolySet([:tick]))
        c = cofree_lazy(p, 0)
        @test_throws BoundsError tree_at(c, 100)
        @test_throws BoundsError tree_at(c, 0)   # 1-based indexing
    end

    @testset "tree_at on multiple indices recovers the carrier" begin
        p = Polynomial(FinPolySet([:run, :halt]),
                       i -> i == :run ? FinPolySet([:tick]) : FinPolySet(Symbol[]))
        c = cofree_lazy(p, 1)
        eager = materialize(c)
        n = length(eager.carrier.positions.elements)
        all_via_tree_at = [tree_at(c, i) for i in 1:n]
        @test Set(all_via_tree_at) == Set(eager.carrier.positions.elements)
    end

    # ============================================================
    # parallel — stretch goal (Q8.1)
    # ============================================================

    @testset "parallel of two lazy cofrees materializes and returns Comonoid" begin
        p = Polynomial(FinPolySet([:run]), _ -> FinPolySet([:tick]))
        c1 = cofree_lazy(p, 1)
        c2 = cofree_lazy(p, 1)
        joint = parallel(c1, c2)
        @test joint isa Comonoid
        # Both inputs got materialized.
        @test is_materialized(c1)
        @test is_materialized(c2)
    end

    # ============================================================
    # Adversarial tests
    # ============================================================

    @testset "adversarial — depth=0 degenerate cofree" begin
        # depth-0: carrier positions are exactly the polynomial's positions.
        p = Polynomial(FinPolySet([:i1, :i2]),
                       _ -> FinPolySet([:a]))
        c = cofree_lazy(p, 0)
        @test validate_comonoid(c)
        eager = materialize(c)
        @test cardinality(eager.carrier.positions) == Finite(2)
    end

    @testset "adversarial — single-position polynomial with empty directions" begin
        # Constant polynomial: p has positions but no directions. Cofree
        # of this is also trivial.
        p = Polynomial(FinPolySet([:c]), _ -> FinPolySet(Symbol[]))
        c = cofree_lazy(p, 5)
        @test validate_comonoid(c)
    end

    @testset "adversarial — cache survives multiple accesses" begin
        # eraser / duplicator / tree_at all share the same cache.
        p = Polynomial(FinPolySet([:run, :halt]),
                       i -> i == :run ? FinPolySet([:tick]) : FinPolySet(Symbol[]))
        c = cofree_lazy(p, 1)
        e1 = eraser(c)
        d1 = duplicator(c)
        t1 = tree_at(c, 1)
        # All three operations after the first don't re-materialize.
        e2 = eraser(c)
        @test e1 === e2  # cached Lens object identity
    end

    @testset "adversarial — clear_cache! is idempotent" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        c = cofree_lazy(p, 1)
        clear_cache!(c)   # before any materialization — no-op
        @test !is_materialized(c)
        materialize(c)
        clear_cache!(c)
        clear_cache!(c)   # second clear is also no-op
        @test !is_materialized(c)
    end

    @testset "adversarial — equal lazy cofrees with independent caches" begin
        # Two LazyCofreeComonoid built from same (p, depth) compare ==
        # but materializing one doesn't materialize the other.
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        c1 = cofree_lazy(p, 1)
        c2 = cofree_lazy(p, 1)
        @test c1 == c2
        materialize(c1)
        @test is_materialized(c1)
        @test !is_materialized(c2)
    end

    @testset "adversarial — materialized state doesn't affect == comparison" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        c1 = cofree_lazy(p, 1)
        c2 = cofree_lazy(p, 1)
        materialize(c1)
        @test c1 == c2  # equality ignores cache state
    end

    @testset "adversarial — large polynomial cofree at small depth still constructs lazily" begin
        # Build a polynomial that would explode at depth 3 (per the
        # Cofree.jl combinatorial table); cofree_lazy at depth 1 should
        # be fine — only depth-1 trees enumerate on materialization.
        p = Polynomial(FinPolySet([:p, :q]),
                       i -> i == :p ? FinPolySet([1, 2]) : FinPolySet([3]))
        c = cofree_lazy(p, 1)
        @test !is_materialized(c)        # truly lazy until queried
        @test validate_comonoid(c)        # answer without materializing
        @test !is_materialized(c)        # confirmed lazy
    end

end
