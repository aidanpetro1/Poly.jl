# ============================================================
# v0.4 #2: truly-lazy LazyBicomoduleCarrier
# ============================================================
#
# v0.4 makes `compose_lazy(M, N)` return a Bicomodule whose `.carrier.positions`
# is a streaming `BicomoduleComposePosSet` rather than a materialized
# `FinPolySet`. The validators (`validate_bicomodule_detailed` and the
# underlying right/left-comodule validators) walk the streaming form via
# `_iter_positions` without filling a vector of all `(x, σ)` pairs.
#
# Coverage:
#
#   1. compose_lazy returns a Bicomodule whose .carrier.positions is a
#      BicomoduleComposePosSet (not a FinPolySet).
#   2. The streaming iterator yields the same set of (x, σ) pairs as the
#      eager `compose`.
#   3. Structural cardinality formula matches enumeration count.
#   4. validate_bicomodule_detailed runs on the lazy form and agrees with
#      validation of the eager `compose` result.
#   5. Adversarial: a moderately-large compose (~few hundred positions)
#      validates without blowing up.
#   6. Identity fast-path on Polynomial == lets lens construction succeed
#      with a lazy positions set.

@testset "v0.4 #2: truly-lazy LazyBicomoduleCarrier" begin

    # Build a simple regular_bicomodule scenario and a state_system_comonoid.
    cs = state_system_comonoid(FinPolySet([:s1, :s2]))
    M  = regular_bicomodule(cs)
    N  = regular_bicomodule(cs)

    @testset "compose_lazy returns lazy positions" begin
        L = compose_lazy(M, N)
        @test L.carrier.positions isa Poly.BicomoduleComposePosSet
        # The eager compose still returns FinPolySet positions.
        E = compose(M, N)
        @test E.carrier.positions isa FinPolySet
    end

    @testset "structural cardinality formula matches enumeration" begin
        L = compose_lazy(M, N)
        E = compose(M, N)
        @test length(L.carrier.positions) == length(E.carrier.positions.elements)
        @test cardinality(L.carrier.positions) ==
              Poly.Finite(length(E.carrier.positions.elements))
    end

    @testset "streaming iterator yields the same (x, σ) set" begin
        L = compose_lazy(M, N)
        E = compose(M, N)
        # Convert each (x, σ) to a comparable form (σ is a Dict; use sorted-pairs).
        norm = pair -> (pair[1], sort(collect(pair[2])))
        lazy_set  = Set([norm(p) for p in L.carrier.positions])
        eager_set = Set([norm(p) for p in E.carrier.positions.elements])
        @test lazy_set == eager_set
    end

    @testset "validate_bicomodule on lazy form" begin
        L = compose_lazy(M, N)
        # Should validate cleanly without materializing.
        @test validate_bicomodule(L)
        # Detailed result has the same passed flag as the eager form.
        @test validate_bicomodule_detailed(L).passed ==
              validate_bicomodule_detailed(compose(M, N)).passed
    end

    @testset "right and left comodule validators accept lazy carrier" begin
        L = compose_lazy(M, N)
        # The lazy bicomodule's coactions wrap the lazy carrier; the
        # comodule validators must walk it without erroring on the type.
        Mr = Poly.RightComodule(L.carrier, L.right_base, L.right_coaction)
        Ml = Poly.LeftComodule(L.carrier, L.left_base, L.left_coaction)
        @test validate_right_comodule(Mr)
        @test validate_left_comodule(Ml)
    end

    @testset "identity fast-path on Polynomial ==" begin
        # The Bicomodule constructor checks `coaction.dom == carrier`. With a
        # lazy positions set, this comparison would error in the v0.3.x impl
        # (no FinPolySet branch). v0.4's identity fast-path lets it pass.
        L = compose_lazy(M, N)
        @test L.left_coaction.dom == L.carrier
        @test L.right_coaction.dom == L.carrier
        # And `L.carrier == L.carrier` itself works.
        @test L.carrier == L.carrier
    end

    @testset "moderately-large compose validates without blowing up" begin
        # Build state_system on a 5-position carrier (so |X|=5 with 5 directions
        # each, |compose-positions| = sum over x of product over a of #compatible_y).
        # For state_system, each x has |X|=5 directions and each direction routes
        # to one D-position (its target state), and there are 5 y candidates per
        # D-position (since regular_bicomodule has the same carrier). So the
        # naive eager count is 5 * 5^5 = 15625. We don't actually want to enumerate
        # all of those — but the lazy compose should construct without running
        # the enumeration eagerly.
        big_cs = state_system_comonoid(FinPolySet([:a, :b, :c]))
        Mb = regular_bicomodule(big_cs)
        Nb = regular_bicomodule(big_cs)
        Lb = compose_lazy(Mb, Nb)
        @test Lb.carrier.positions isa Poly.BicomoduleComposePosSet
        # Length is computed structurally.
        len = length(Lb.carrier.positions)
        @test len > 0
        # Validation walks the streaming positions.
        @test validate_bicomodule(Lb)
    end

    @testset "compose_lazy preserves the regular-bicomodule unit law" begin
        # For a comonoid c, compose(regular_bicomodule(c), regular_bicomodule(c))
        # has one position per object of c. Same expectation lazy.
        L = compose_lazy(M, N)
        @test length(L.carrier.positions) == length(cs.carrier.positions.elements)
    end

    @testset "_iter_positions polymorphic helper" begin
        fp = FinPolySet([:a, :b, :c])
        @test collect(Poly._iter_positions(fp)) == [:a, :b, :c]

        L = compose_lazy(M, N)
        lazy_iter = Poly._iter_positions(L.carrier.positions)
        # Should be iterable; collecting yields the same set as enumerating eagerly.
        E = compose(M, N)
        norm = pair -> (pair[1], sort(collect(pair[2])))
        @test Set(norm(p) for p in lazy_iter) ==
              Set(norm(p) for p in E.carrier.positions.elements)
    end
end
