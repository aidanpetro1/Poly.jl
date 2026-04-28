# ============================================================
# Extensions v1, PR #5: subst_targeted_lens and subst_targeted_coaction
# ============================================================
#
# Coverage:
#
#   1. subst_targeted_lens produces a Lens whose cod = subst(p, q)
#   2. The on_dir callback receives unpacked (x, a, b) instead of (x, ab)
#   3. Lens equality vs. a manually-constructed equivalent
#   4. subst_targeted_coaction with side=:left
#   5. subst_targeted_coaction with side=:right
#   6. Invalid side raises
#   7. End-to-end: build a comonoid duplicator via the helper and validate

@testset "Extensions v1, PR #5: subst_targeted_lens" begin

    @testset "produces a Lens with cod = subst(p, q)" begin
        # Tiny p, q.
        p = Polynomial(FinPolySet([:i1]), _ -> FinPolySet([:a]))
        q = Polynomial(FinPolySet([:j1]), _ -> FinPolySet([:b]))
        dom = Polynomial(FinPolySet([:x]), _ -> FinPolySet([:dx]))
        f = subst_targeted_lens(dom, p, q,
                x -> (:i1, Dict(:a => :j1)),
                (x, a, b) -> :dx)
        @test f isa Lens
        @test f.dom == dom
        @test f.cod == subst(p, q)
    end

    @testset "on_dir receives unpacked (x, a, b)" begin
        # The helper's contract: when its returned Lens is called with
        # `(x, (a, b))` on its on_directions, the user callback should
        # receive `(x, a, b)` — three arguments, not (x, ab) as a tuple.
        # We verify this by passing an echo callback that records the
        # arguments it sees.
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a1, :a2]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:b1]) : FinPolySet([:b2]))
        # The dom's direction-set must be permissive enough to receive
        # whatever the callback returns — use Symbol so we can return any.
        dom = Polynomial(FinPolySet([:x]),
                          _ -> FinPolySet([:any]))
        seen_args = Tuple[]
        f = subst_targeted_lens(dom, p, q,
                x -> (:i, Dict(:a1 => :j1, :a2 => :j2)),
                (x, a, b) -> begin
                    push!(seen_args, (x, a, b))
                    :any
                end)
        # Drive the lens's on_directions with explicit (a, b) tuples.
        # Whatever jbar happens to be encoded in the cod's positions, the
        # callback should still receive its (x, a, b) form unpacked.
        f.on_directions.f(:x).f((:a1, :b1))
        @test (:x, :a1, :b1) in seen_args
        # Try a couple more arg shapes.
        f.on_directions.f(:x).f((:a2, :b2))
        @test (:x, :a2, :b2) in seen_args
        # The helper unpacks ab unconditionally — that's the contract.
    end

    @testset "matches manual Lens construction" begin
        # Same lens built two ways: helper vs. manual.
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        q = Polynomial(FinPolySet([:j]), _ -> FinPolySet([:b]))
        dom = Polynomial(FinPolySet([:x]), _ -> FinPolySet([:dx]))
        f_helper = subst_targeted_lens(dom, p, q,
                x -> (:i, Dict(:a => :j)),
                (x, a, b) -> :dx)
        f_manual = Lens(dom, subst(p, q),
                        x -> (:i, Dict(:a => :j)),
                        (x, ab) -> :dx)
        @test f_helper == f_manual
    end

    @testset "subst_targeted_coaction side=:left" begin
        S = FinPolySet([:s1, :s2])
        c = state_system_comonoid(S)
        # Build the duplicator (a left-coaction shape: carrier → cL ▷ carrier
        # where cL = c.carrier here) via the helper.
        carrier = c.carrier
        dup = subst_targeted_coaction(carrier, c,
                s -> (s, Dict(t => t for t in S.elements)),
                (s, a, b) -> b;
                side = :left)
        @test dup isa Lens
        @test dup.dom == carrier
        @test dup.cod == subst(c.carrier, carrier)
        # Behaviorally identical to c.duplicator on the on_directions side.
        for s in S.elements
            for a in S.elements, b in S.elements
                @test dup.on_directions.f(s).f((a, b)) ==
                      c.duplicator.on_directions.f(s).f((a, b))
            end
        end
    end

    @testset "subst_targeted_coaction side=:right" begin
        S = FinPolySet([:s1, :s2])
        c = state_system_comonoid(S)
        carrier = c.carrier
        # A right-coaction shape: carrier → carrier ▷ cR where cR = c.carrier.
        co = subst_targeted_coaction(carrier, c,
                s -> (s, Dict(t => t for t in S.elements)),
                (s, a, b) -> b;
                side = :right)
        @test co isa Lens
        @test co.cod == subst(carrier, c.carrier)
    end

    @testset "subst_targeted_coaction rejects invalid side" begin
        S = FinPolySet([:s])
        c = state_system_comonoid(S)
        @test_throws ArgumentError subst_targeted_coaction(c.carrier, c,
                s -> (s, Dict(s => s)),
                (s, a, b) -> b;
                side = :sideways)
    end

    @testset "end-to-end: build comonoid duplicator via helper" begin
        # Use subst_targeted_lens to construct a state_system_comonoid's
        # duplicator from scratch and verify it produces a valid Comonoid.
        S = FinPolySet([:s1, :s2, :s3])
        carrier = state_system(S)
        eraser = Lens(carrier, y, _ -> :pt, (s, _) -> s)   # do_nothing_section
        duplicator = subst_targeted_lens(carrier, carrier, carrier,
                s -> (s, Dict(t => t for t in S.elements)),
                (s, a, b) -> b)
        c = Comonoid(carrier, eraser, duplicator)
        @test c isa Comonoid
        @test validate_comonoid(c)
    end

end  # @testset "Extensions v1, PR #5: subst_targeted_lens"
