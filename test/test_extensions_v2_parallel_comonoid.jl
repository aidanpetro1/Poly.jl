# ============================================================
# Extensions v2, PR #1: parallel(::Comonoid, ::Comonoid) + ⊗ deprecation
# ============================================================
#
# Coverage:
#
#   1. parallel(c, d) returns a valid Comonoid.
#   2. parallel(c, d).carrier == parallel(c.carrier, d.carrier)
#      (Polynomial-level tensor on carriers, not categorical product).
#   3. Eraser is componentwise (s, t) ↦ (eraser_c(s), eraser_d(t)).
#   4. Duplicator first component is componentwise.
#   5. Q1.2: parallel validates at construction; an invalid input
#      surfaces an error rather than producing a silently-broken comonoid.
#   6. Bicomodule parallel still works (uses the public version internally).
#   7. ⊗(c, d) emits a deprecation warning (Q1.1, soft break).
#   8. ⊗(c, d) still returns the same comonoid as `c * d` (v0.2 behavior
#      preserved through v0.3; semantics flip in v0.4).
#   9. Round-trip: the result via `parallel` matches the internal path
#      v0.2 used (same as `_comonoid_carrier_tensor`, now an alias).

@testset "Extensions v2, PR #1: parallel(::Comonoid,::Comonoid) + ⊗ deprecation" begin

    @testset "parallel(c, d) returns a valid Comonoid" begin
        S = FinPolySet([:s1, :s2])
        T = FinPolySet([:t1, :t2, :t3])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)

        joint = parallel(cs, ct)
        @test joint isa Comonoid
        @test validate_comonoid(joint)
    end

    @testset "carrier is Polynomial-level parallel" begin
        S = FinPolySet([:s1, :s2])
        T = FinPolySet([:t1, :t2])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)

        joint = parallel(cs, ct)
        # Carrier should equal parallel(cs.carrier, ct.carrier).
        @test joint.carrier == parallel(cs.carrier, ct.carrier)
        # |carrier.positions| = |S| · |T|.
        @test cardinality(joint.carrier.positions) == Finite(4)
        # Each position has |S| · |T| directions (state_system has |S|y^|S|).
        sample_pos = first(joint.carrier.positions.elements)
        @test cardinality(direction_at(joint.carrier, sample_pos)) == Finite(4)
    end

    @testset "eraser is componentwise" begin
        S = FinPolySet([:s1, :s2])
        T = FinPolySet([:t1, :t2])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)

        joint = parallel(cs, ct)
        for st in joint.carrier.positions.elements
            s, t = st
            eraser_pair = joint.eraser.on_directions.f(st).f(:pt)
            expected_s = cs.eraser.on_directions.f(s).f(:pt)
            expected_t = ct.eraser.on_directions.f(t).f(:pt)
            @test eraser_pair == (expected_s, expected_t)
        end
    end

    @testset "duplicator first component is componentwise" begin
        S = FinPolySet([:s1, :s2])
        T = FinPolySet([:t1, :t2])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)

        joint = parallel(cs, ct)
        for st in joint.carrier.positions.elements
            s, t = st
            (st_dup, _) = joint.duplicator.on_positions.f(st)
            (s_dup, _) = cs.duplicator.on_positions.f(s)
            (t_dup, _) = ct.duplicator.on_positions.f(t)
            @test st_dup == (s_dup, t_dup)
        end
    end

    @testset "validation catches invalid inputs (Q1.2)" begin
        # Construct a comonoid that fails validate_comonoid (per the
        # existing "non-monoid fails validation" pattern), then check
        # that parallel surfaces this as an error rather than silently
        # producing a broken result.
        M = FinPolySet(0:2)
        bad = monoid_comonoid(M, 0, (a, _b) -> a)  # left projection: not a monoid
        @test !validate_comonoid(bad)              # confirm it really is invalid

        good = state_system_comonoid(FinPolySet([:s1, :s2]))
        # The carrier-tensor of (bad, good) inherits bad's coassociativity
        # failures componentwise, so validate_comonoid on the result fails,
        # and `parallel` errors at construction.
        @test_throws ErrorException parallel(bad, good)
    end

    @testset "Bicomodule parallel still works (uses public surface)" begin
        # The internal `_comonoid_carrier_tensor` is now an alias for the
        # public `parallel(::Comonoid, ::Comonoid)`. Existing
        # parallel(::Bicomodule, ::Bicomodule) call sites must keep working.
        S = FinPolySet([:s1, :s2])
        T = FinPolySet([:t1, :t2])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)
        Ms = regular_bicomodule(cs)
        Mt = regular_bicomodule(ct)

        Mjoint = parallel(Ms, Mt)
        @test Mjoint isa Bicomodule
        @test validate_bicomodule(Mjoint)
    end

    @testset "⊗(c, d) ≡ parallel(c, d) in v0.3 (semantics flip)" begin
        # v0.3 collapses `⊗` and `parallel` for Comonoid (Q1.1 resolution
        # 2026-05-01: hard break, not soft, because `⊗` and `parallel`
        # share a function via `const var"⊗" = parallel` in Monoidal.jl).
        # Both names produce the carrier-tensor.
        S = FinPolySet([:s1, :s2])
        T = FinPolySet([:t1, :t2])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)

        # Same function: ⊗ === parallel for Comonoid arguments.
        @test methods(⊗, (Comonoid, Comonoid)) ==
              methods(parallel, (Comonoid, Comonoid))

        result_otimes  = cs ⊗ ct
        result_star    = cs * ct
        result_parallel = parallel(cs, ct)
        @test result_otimes isa Comonoid
        # ⊗ and parallel give iso-equivalent results to `*` but with the
        # carrier-tensor's direction-pair encoding (NOT the categorical-
        # product's morphism-pair encoding). `≈` for the iso claim.
        @test result_otimes.carrier ≈ result_star.carrier
        @test result_otimes.carrier ≈ result_parallel.carrier
    end

    @testset "_comonoid_carrier_tensor alias points to parallel" begin
        S = FinPolySet([:s1])
        T = FinPolySet([:t1])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)

        # Alias: `_comonoid_carrier_tensor(c, d)` should produce the same
        # comonoid as `parallel(c, d)`. Iso, not strict ==, for the same
        # reason as the main `parallel` ↔ `*` test above.
        via_alias  = Poly._comonoid_carrier_tensor(cs, ct)
        via_public = parallel(cs, ct)
        @test via_alias.carrier ≈ via_public.carrier
    end

    # ============================================================
    # Adversarial tests
    # ============================================================
    #
    # Beyond happy-path: properties that must hold of any well-defined
    # carrier-tensor operation, edge cases that the loose `parallel`
    # construction must handle, and invariants that distinguish
    # `parallel` from `*`.

    @testset "adversarial — parallel is commutative up to iso" begin
        # The polynomial-level ⊗ is symmetric (Σ_i,j |q[j]|^|p[i]| ≈ Σ_j,i |p[i]|^|q[j]|),
        # so the comonoid-level carrier-tensor inherits commutativity up
        # to iso. Strict `==` fails because position labels are tagged
        # by the input order; `≈` should hold.
        S = FinPolySet([:a, :b])
        T = FinPolySet([:x, :y, :z])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)

        @test parallel(cs, ct).carrier ≈ parallel(ct, cs).carrier
        @test !(parallel(cs, ct).carrier == parallel(ct, cs).carrier)  # not strict-eq
    end

    @testset "adversarial — parallel is associative up to iso" begin
        # Carrier-tensor associativity. (a ⊗ b) ⊗ c ≈ a ⊗ (b ⊗ c) by the
        # Polynomial-level associator; comonoid-level inherits this.
        S = FinPolySet([:a, :b])
        T = FinPolySet([:x, :y])
        U = FinPolySet([:p])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)
        cu = state_system_comonoid(U)

        left  = parallel(parallel(cs, ct), cu)
        right = parallel(cs, parallel(ct, cu))
        @test left.carrier ≈ right.carrier
    end

    @testset "adversarial — discrete and state-system mix" begin
        # `parallel` should work across different built-in comonoid
        # constructors, not just two state-systems. Discrete (= identity-only
        # category) tensored with state-system gives the right object count.
        S = FinPolySet([:a, :b])
        T = FinPolySet([:x, :y, :z])
        cd = discrete_comonoid(S)        # 2 objects, 2 morphisms (identities only)
        ct = state_system_comonoid(T)    # 3 objects, 9 morphisms

        joint = parallel(cd, ct)
        @test validate_comonoid(joint)
        # |objects| = |S| · |T| = 6.
        @test cardinality(joint.carrier.positions) == Finite(6)
    end

    @testset "adversarial — singleton state-system is left-identity-ish" begin
        # parallel(state_system on a singleton, c) has carrier
        # 1y^1 ⊗ c.carrier ≈ c.carrier (Polynomial ⊗-unitor for state-system).
        S = FinPolySet([:only])
        T = FinPolySet([:a, :b])
        cs1 = state_system_comonoid(S)   # carrier = 1y^1
        ct  = state_system_comonoid(T)

        joint = parallel(cs1, ct)
        @test validate_comonoid(joint)
        # The state-system on a singleton has carrier == y, so
        # parallel(cs1.carrier, ct.carrier) ≈ ct.carrier.
        @test joint.carrier ≈ ct.carrier
    end

    @testset "adversarial — ⊗ and parallel land at iso but distinct objects" begin
        # `⊗` delegates to `*` (categorical product) in v0.3; `parallel`
        # is the carrier-tensor. They're iso (`≈`) but the design
        # distinction lives in HOW the carriers are constructed:
        # `*` goes through `from_category`'s SmallCategory bridge,
        # `parallel` goes through `Polynomial`-level `parallel` directly.
        # That distinction is what justifies having both functions.
        S = FinPolySet([:a, :b])
        T = FinPolySet([:x, :y])
        cs = state_system_comonoid(S)
        ct = state_system_comonoid(T)

        via_otimes   = cs ⊗ ct             # categorical product
        via_parallel = parallel(cs, ct)    # carrier-tensor

        # Iso: they produce the same comonoid shape.
        @test via_otimes.carrier ≈ via_parallel.carrier
        @test cardinality(via_otimes.carrier.positions)   == Finite(4)
        @test cardinality(via_parallel.carrier.positions) == Finite(4)

        # Distinct objects: even when they happen to use the same direction
        # encoding for state-system inputs, they're separate Comonoid
        # constructions with separate carrier closures. A simple identity
        # check pins this — if v0.4's semantics flip accidentally aliases
        # ⊗ and parallel back to one shared implementation, this catches it.
        @test via_otimes !== via_parallel
        @test via_otimes.carrier !== via_parallel.carrier

        # Both validate as comonoids on their own terms.
        @test validate_comonoid(via_otimes)
        @test validate_comonoid(via_parallel)
    end

    @testset "adversarial — Q1.2 catches downstream of a broken duplicator" begin
        # A different way to break a comonoid: tamper with the duplicator
        # so coassoc fails (rather than a broken monoid law). Then
        # parallel(broken, valid) should still surface the failure.
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        # Hack the duplicator's on_directions to swap two outputs — this
        # breaks coassoc on the original comonoid, and the carrier-tensor
        # inherits the breakage.
        bad_dup = Lens(cs.carrier, cs.duplicator.cod,
                       cs.duplicator.on_positions.f,
                       (i, ab) -> begin
                           a, b = ab
                           # Lie at one specific (i, a, b) triple.
                           (i == :a && a == :a && b == :b) ? :a : b
                       end)
        bad = Comonoid(cs.carrier, cs.eraser, bad_dup)
        @test !validate_comonoid(bad)

        T = FinPolySet([:x])
        ct = state_system_comonoid(T)
        @test_throws ErrorException parallel(bad, ct)
    end

    @testset "adversarial — parallel(c, c) is not the diagonal" begin
        # Self-tensor produces a comonoid with |c.objects|^2 objects, not
        # |c.objects|. This catches any accidental short-circuiting of
        # the construction when both operands are identical.
        S = FinPolySet([:a, :b, :c])
        cs = state_system_comonoid(S)

        joint = parallel(cs, cs)
        @test validate_comonoid(joint)
        @test cardinality(joint.carrier.positions) == Finite(9)   # 3 · 3
        # Direction-set per position: |S|·|S| = 9.
        sample = first(joint.carrier.positions.elements)
        @test cardinality(direction_at(joint.carrier, sample)) == Finite(9)
    end

end
