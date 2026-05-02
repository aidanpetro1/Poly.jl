# ============================================================
# Extensions v2, PR #12: representable accepts Vector / AbstractSet
# ============================================================
#
# `representable` previously required a `PolySet`; users with a Vector
# or Set in hand had to wrap it in `FinPolySet(...)` first. The Vector
# and AbstractSet overloads forward through `FinPolySet`, so calls on
# raw element-collections are now one less hop.

@testset "Extensions v2, PR #12: representable(::Vector) / (::AbstractSet)" begin

    @testset "Vector forwards to FinPolySet" begin
        v = [:a, :b, :c]
        @test representable(v) == representable(FinPolySet(v))
    end

    @testset "Set forwards to FinPolySet" begin
        # NOTE: Set ordering isn't guaranteed, so compare via cardinality
        # and elements-as-a-set rather than == on Polynomials. The promise
        # is "equivalent up to direction-set element ordering."
        s = Set([:a, :b, :c])
        p = representable(s)
        @test cardinality(p.positions) == Finite(1)
        only_pos = first(p.positions.elements)
        @test Set(direction_at(p, only_pos).elements) == s
    end

    @testset "Integer Vector" begin
        @test representable([1, 2, 3]) == representable(FinPolySet([1, 2, 3]))
    end

    @testset "empty Vector — direction-set ∅, polynomial is y^0 ≈ 1" begin
        # representable(∅) = y^0 ≅ 1 (the constant-one polynomial)
        @test cardinality(representable(Symbol[]).positions) == Finite(1)
        @test cardinality(direction_at(representable(Symbol[]),
                                       first(representable(Symbol[]).positions.elements))) == Finite(0)
    end

    # ============================================================
    # Adversarial tests
    # ============================================================

    @testset "adversarial — Vector with duplicates dedupes via FinPolySet" begin
        # FinPolySet's constructor calls `unique`, so duplicates collapse.
        # representable on a Vector with duplicates should match
        # representable on the deduplicated FinPolySet.
        v_dups = [:a, :b, :a, :c, :b]
        @test representable(v_dups) == representable(FinPolySet([:a, :b, :c]))
        # Direction-set cardinality should be 3, not 5.
        p = representable(v_dups)
        @test cardinality(direction_at(p, first(p.positions.elements))) == Finite(3)
    end

    @testset "adversarial — single-element Vector is the linear y^1 ≈ y" begin
        # representable([x]) = y^1 ≈ y.
        @test representable([:only]) ≈ y
    end

    @testset "adversarial — heterogeneous element types via Any[]" begin
        # Mixing types is allowed (FinPolySet{Any}); no method ambiguity
        # surface from the new overloads.
        v = Any[:sym, 42, "str"]
        p = representable(v)
        @test cardinality(direction_at(p, first(p.positions.elements))) == Finite(3)
    end

    @testset "adversarial — original PolySet method still wins on ambiguity" begin
        # Passing a FinPolySet directly should hit the PolySet overload,
        # NOT recurse via the Vector overload (which would silently
        # double-wrap).
        s = FinPolySet([:a, :b])
        @test representable(s) == representable([:a, :b])
        # And that the result has direction-set s itself, not nested.
        p = representable(s)
        @test direction_at(p, first(p.positions.elements)) == s
    end

    @testset "adversarial — Set with non-symbol elements" begin
        # AbstractSet overload; verifies `collect` produces something
        # FinPolySet can ingest.
        s = Set([1, 2, 3, 4])
        p = representable(s)
        @test cardinality(direction_at(p, first(p.positions.elements))) == Finite(4)
        @test Set(direction_at(p, first(p.positions.elements)).elements) == s
    end

    @testset "adversarial — large Vector still constructs in one hop" begin
        # Smoke-test: 1000-element Vector. Should construct without
        # iterating per-element more than once (FinPolySet's `unique`).
        v = collect(1:1000)
        p = representable(v)
        @test cardinality(direction_at(p, first(p.positions.elements))) == Finite(1000)
    end

end
