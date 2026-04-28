# ============================================================
# Extensions v1, PR #3: n-ary flat coproduct
# ============================================================
#
# Coverage:
#
#   1. Edge cases: empty, single operand
#   2. Flat tags vs. nested binary-+ tags
#   3. Cardinality equivalence with binary + chain
#   4. coproduct on lenses
#   5. flatten_coproduct round-trip and idempotence

@testset "Extensions v1, PR #3: n-ary coproduct" begin

    @testset "edge cases" begin
        @test coproduct() == zero_poly
        p = Polynomial(FinPolySet([:a, :b]), _ -> FinPolySet([:x]))
        @test coproduct(p) === p
    end

    @testset "flat tags for n ≥ 2" begin
        pa = Polynomial(FinPolySet([:a1, :a2]), _ -> FinPolySet([:da]))
        pb = Polynomial(FinPolySet([:b1]),       _ -> FinPolySet([:db1, :db2]))
        pc = Polynomial(FinPolySet([:c1, :c2, :c3]), _ -> FinPolySet([:dc]))

        cp = coproduct(pa, pb, pc)
        # Flat tags: (1, _), (2, _), (3, _).
        @test cp.positions isa FinPolySet
        first_components = Set(t[1] for t in cp.positions.elements)
        @test first_components == Set([1, 2, 3])
        # Each operand contributes its positions count.
        @test length(cp.positions.elements) == 2 + 1 + 3
    end

    @testset "cardinality matches binary + chain" begin
        pa = Polynomial(FinPolySet([:a1, :a2]), _ -> FinPolySet([:da]))
        pb = Polynomial(FinPolySet([:b1]),       _ -> FinPolySet([:db1, :db2]))
        pc = Polynomial(FinPolySet([:c1, :c2, :c3]), _ -> FinPolySet([:dc]))

        cp_nary  = coproduct(pa, pb, pc)
        cp_binary = pa + pb + pc

        @test cardinality(cp_nary.positions) == cardinality(cp_binary.positions)
        # Direction-set sizes per position match (modulo tag re-encoding):
        # cardinality of `apply` to a sample set should agree.
        X = FinPolySet([:x1, :x2])
        @test cardinality_of_apply(cp_nary, X) == cardinality_of_apply(cp_binary, X)
    end

    @testset "directions routed correctly" begin
        pa = Polynomial(FinPolySet([:a1]), _ -> FinPolySet([:da]))
        pb = Polynomial(FinPolySet([:b1]), _ -> FinPolySet([:db1, :db2]))
        pc = Polynomial(FinPolySet([:c1]), _ -> FinPolySet(Symbol[]))

        cp = coproduct(pa, pb, pc)
        @test direction_at(cp, (1, :a1)) == FinPolySet([:da])
        @test direction_at(cp, (2, :b1)) == FinPolySet([:db1, :db2])
        @test direction_at(cp, (3, :c1)) == FinPolySet(Symbol[])
    end

    @testset "coproduct on lenses" begin
        # Identity lenses on three small polynomials, n-ary coproduct should
        # itself be the identity on the n-ary coproduct of the polynomials.
        pa = Polynomial(FinPolySet([:a]), _ -> FinPolySet([:da]))
        pb = Polynomial(FinPolySet([:b]), _ -> FinPolySet([:db]))
        pc = Polynomial(FinPolySet([:c]), _ -> FinPolySet([:dc]))

        fa = identity_lens(pa)
        fb = identity_lens(pb)
        fc = identity_lens(pc)

        f_combined = coproduct(fa, fb, fc)
        @test f_combined.dom == coproduct(pa, pb, pc)
        @test f_combined.cod == coproduct(pa, pb, pc)
        # Sanity: applying on each operand's tag returns the same tag.
        @test f_combined.on_positions.f((1, :a)) == (1, :a)
        @test f_combined.on_positions.f((2, :b)) == (2, :b)
        @test f_combined.on_positions.f((3, :c)) == (3, :c)
    end

    @testset "flatten_coproduct on a binary + chain" begin
        pa = Polynomial(FinPolySet([:a1, :a2]), _ -> FinPolySet([:da]))
        pb = Polynomial(FinPolySet([:b1]),       _ -> FinPolySet([:db]))
        pc = Polynomial(FinPolySet([:c1, :c2]), _ -> FinPolySet([:dc1, :dc2]))

        chain    = pa + pb + pc       # left-associated: (pa + pb) + pc
        flat     = flatten_coproduct(chain)
        expected = coproduct(pa, pb, pc)

        # Flatten produces flat tags that match coproduct.
        @test Set(flat.positions.elements) == Set(expected.positions.elements)
        # Direction lookup agrees.
        for key in flat.positions.elements
            @test direction_at(flat, key) == direction_at(expected, key)
        end
    end

    @testset "flatten_coproduct on a 4-chain" begin
        # Stress-test the depth-3 case (p1 has 3 nested 1s).
        p1 = Polynomial(FinPolySet([:s1]), _ -> FinPolySet([:d1]))
        p2 = Polynomial(FinPolySet([:s2]), _ -> FinPolySet([:d2]))
        p3 = Polynomial(FinPolySet([:s3]), _ -> FinPolySet([:d3]))
        p4 = Polynomial(FinPolySet([:s4]), _ -> FinPolySet([:d4]))

        chain = p1 + p2 + p3 + p4
        flat = flatten_coproduct(chain)
        expected = coproduct(p1, p2, p3, p4)

        @test Set(flat.positions.elements) == Set(expected.positions.elements)
        for key in flat.positions.elements
            @test direction_at(flat, key) == direction_at(expected, key)
        end
    end

    @testset "flatten_coproduct idempotent on flat polynomial" begin
        # When positions are NOT (Int, _) tuples whose first element is 1 or 2,
        # flatten_coproduct should leave the polynomial structurally equivalent
        # — a single position with no chain, treated as :leftmost depth 0.
        p = Polynomial(FinPolySet([:bare]), _ -> FinPolySet([:dx]))
        flat = flatten_coproduct(p)
        # Should re-tag :bare as (1, :bare) since the walker terminates at
        # depth 0 on the bare symbol — kind=:leftmost, operand=1.
        @test flat.positions.elements == [(1, :bare)]
    end

    @testset "flatten_coproduct documented limitation: (Int, _)-tagged originals" begin
        # The structural walker can't distinguish "operand 1's original
        # position is (1, :inner)" from "operand 1 of a 2-chain wrapping
        # :inner". This is documented in flatten_coproduct's docstring; this
        # test is a regression marker so future refactors don't silently
        # change the behavior.
        #
        # Construct a polynomial whose positions are (1, _) tuples *as the
        # natural encoding* (e.g. a coproduct of a coproduct, used as input
        # to flatten as if it were the outer chain). The walker descends
        # past what was supposed to be the leaf.
        inner = Polynomial(FinPolySet([(1, :payload), (2, :other)]),
                           _ -> FinPolySet([:dx]))
        flat = flatten_coproduct(inner)
        # The walker descends through (1, :payload) treating :payload as the
        # leaf — which mis-classifies. The (2, :other) position is treated
        # correctly as having hit a 2 at depth 0. Across both positions
        # max_depth=1 so n=2.
        # - (1, :payload) → :leftmost at depth 1 → operand 1 with leaf :payload
        # - (2, :other)   → :hit_2 at depth 0    → operand n - 0 = 2 with leaf :other
        # The result happens to be flat tags but the positions of "operand 1"
        # have lost the original (1, ...) wrapping — that's the misclassification.
        @test (1, :payload) in flat.positions.elements
        @test (2, :other) in flat.positions.elements
        # If the user wanted the original (1, :payload) preserved, they'd need
        # to use coproduct(...) directly rather than relying on flatten.
    end

end  # @testset "Extensions v1, PR #3: n-ary coproduct"
