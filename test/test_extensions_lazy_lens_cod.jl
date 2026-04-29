# ============================================================
# Extensions v1.1: Lazy `Lens.cod` (AbstractPolynomial widening)
# ============================================================
#
# Coverage:
#
#   1. Lens construction with a LazySubst cod (no enumeration)
#   2. Lens equality across lazy/concrete cods
#   3. Lens display works with a lazy cod
#   4. Bicomodule constructor accepts lenses with lazy cods
#   5. Joint Bicomodule construction at scale that would OOM under
#      eager subst — mirrors the PolyCDS v1.1 reviewer scenario.
#   6. Comonoid ⊗ / + on built-ins with the new lazy-cod duplicator
#
# Motivation: prior to this widening, `Lens.cod::Polynomial` forced
# every Lens-typed coaction or duplicator to materialize its
# substitution-polynomial codomain. For carriers around 16 positions
# with 25 directions each, `subst(carrier, carrier)` has 16 × 16^25 ≈
# 10^31 positions — far past memory limits.

@testset "Extensions v1.1: lazy Lens.cod" begin

    # ============================================================
    # 1. Lens construction with a LazySubst cod
    # ============================================================
    @testset "Lens accepts LazySubst cod (no enumeration)" begin
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:x]) : FinPolySet([:y, :z]))

        lazy_cod = subst_lazy(p, q)

        # The cod is lazy; building a lens against it must not enumerate.
        # Using identity-shaped on_pos/on_dir with dom == positions(lazy_cod)
        # would require iterating SubstPolySet, which is intentionally
        # un-iterable. So we use `p` as dom and an on_pos that produces
        # a (i, jbar) pair structurally matching the LazySubst encoding.
        f = Lens(p, lazy_cod,
                 i -> begin
                     # any j̄ : p[i] → q.positions; pick the constant-j1 map.
                     Di = direction_at(p, i)::FinPolySet
                     (i, Dict(a => :j1 for a in Di.elements))
                 end,
                 (i, ab) -> begin
                     a, b = ab
                     a   # land back in p[i]
                 end)
        @test f.cod isa LazySubst
        @test f.cod === lazy_cod
        # cod.positions reports as SubstPolySet; verifying without enumeration.
        @test positions(f.cod) isa Poly.SubstPolySet
    end

    # ============================================================
    # 2. Lens equality across lazy/concrete cods
    # ============================================================
    @testset "Lens equality with lazy cod" begin
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:x]) : FinPolySet([:y, :z]))

        # Two lenses with structurally-equal LazySubst cods compare equal.
        on_pos_fn = i -> (i, Dict(a => :j1 for a in direction_at(p, i).elements))
        on_dir_fn = (i, ab) -> ab[1]

        f1 = Lens(p, subst_lazy(p, q), on_pos_fn, on_dir_fn)
        f2 = Lens(p, subst_lazy(p, q), on_pos_fn, on_dir_fn)
        @test f1 == f2

        # Cross-type equality: LazySubst cod compared with eager subst.
        # Backward-compat with `lens.cod == subst(p, q)` style asserts.
        @test f1.cod == subst(p, q)
        @test subst(p, q) == f1.cod
    end

    # ============================================================
    # 3. Lens display works with a lazy cod
    # ============================================================
    @testset "Lens display with lazy cod" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        q = Polynomial(FinPolySet([:j]), _ -> FinPolySet([:b]))
        lazy = subst_lazy(p, q)
        f = Lens(p, lazy,
                 i -> (i, Dict(a => :j for a in direction_at(p, i).elements)),
                 (_, ab) -> ab[1])

        # show(::IO, ::Lens) uses show on the cod; LazySubst's show produces
        # something like "LazySubst(p ▷ q)".
        s = sprint(show, f)
        @test occursin("Lens(", s)
        @test occursin("LazySubst", s) || occursin("▷", s)

        # MIME"text/plain" goes through polybox; should not crash and
        # shouldn't materialize the cod.
        s_plain = sprint(show, MIME"text/plain"(), f)
        @test !isempty(s_plain)
    end

    # ============================================================
    # 4. Bicomodule constructor accepts lenses with lazy cods
    # ============================================================
    @testset "Bicomodule accepts lazy-cod coactions" begin
        # Reuse a small state-system to get a known-good comonoid + duplicator,
        # but rebuild the duplicator with an explicit subst_lazy cod.
        S = FinPolySet([:s1, :s2])
        cs = state_system_comonoid(S)
        # cs.duplicator.cod is now LazySubst (after the Comonoid.jl fix).
        @test cs.duplicator.cod isa LazySubst

        # regular_bicomodule takes the duplicator twice; constructor should
        # still accept it (via is_subst_of's lazy short-circuit).
        B = regular_bicomodule(cs)
        @test B isa Bicomodule
        @test validate_bicomodule(B)
    end

    # ============================================================
    # 5. Joint Bicomodule construction at scale (PolyCDS v1.1 mirror)
    # ============================================================
    @testset "Joint Bicomodule construction at scale" begin
        # Two state-systems whose tensor would explode under eager subst.
        # state_system(S) has |S| positions × |S| directions; tensoring two
        # state systems gives a carrier with |S1|·|S2| positions × |S1|·|S2|
        # directions per position. For |S1| = 4, |S2| = 5 we get a 20-position,
        # 20-direction-each carrier, so subst(carrier, carrier) eagerly would
        # have 20 · 20^20 ≈ 10^26 positions. Lazy keeps this constant-time.
        S1 = FinPolySet([:a1, :a2, :a3, :a4])
        S2 = FinPolySet([:b1, :b2, :b3, :b4, :b5])

        c1 = state_system_comonoid(S1)
        c2 = state_system_comonoid(S2)

        # Pre-tensoring sanity: the duplicators are lazy.
        @test c1.duplicator.cod isa LazySubst
        @test c2.duplicator.cod isa LazySubst

        M1 = regular_bicomodule(c1)
        M2 = regular_bicomodule(c2)

        # Build the joint bicomodule. With eager subst this would OOM.
        # With subst_lazy at the three Cofree.jl call sites, this is fast.
        Mjoint = parallel(M1, M2)
        @test Mjoint isa Bicomodule

        # Carrier sanity: 4 × 5 = 20 positions.
        @test cardinality(Mjoint.carrier.positions) == Finite(20)
        # Direction-set at any position should be 4 × 5 = 20.
        sample_pos = first(Mjoint.carrier.positions.elements)
        @test cardinality(direction_at(Mjoint.carrier, sample_pos)) == Finite(20)

        # The new coactions and the new duplicator on the joint carrier all
        # have lazy cods.
        @test Mjoint.left_coaction.cod isa LazySubst
        @test Mjoint.right_coaction.cod isa LazySubst

        # Validate the bicomodule axioms element-wise. The validator iterates
        # over carrier and base positions/directions only — 20 × 20 outer
        # × inner triples — not the substitution polynomial.
        result = validate_bicomodule_detailed(Mjoint)
        @test result.passed
    end

    # ============================================================
    # 6. Comonoid ⊗ / + on built-ins exercising the lazy-cod path
    # ============================================================
    @testset "Comonoid arithmetic with lazy duplicators" begin
        # `from_category` (the bridge `Comonoid +`/`*`/`⊗` go through) now
        # uses subst_lazy for the duplicator's cod. Validate the result.
        S = FinPolySet([:a, :b])
        T = FinPolySet([:x, :y_])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)

        sum_c = cs + ct
        @test sum_c isa Comonoid
        @test sum_c.duplicator.cod isa LazySubst
        @test validate_comonoid(sum_c)

        prod_c = cs * ct
        @test prod_c isa Comonoid
        @test prod_c.duplicator.cod isa LazySubst
        @test validate_comonoid(prod_c)
    end

end  # @testset "Extensions v1.1: lazy Lens.cod"
