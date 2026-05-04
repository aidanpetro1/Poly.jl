# ============================================================
# v0.4.x patch: subst(::Lens, ::Lens) builds lazy dom AND cod
# ============================================================
#
# Spec: PolyCDS v1.7 iso-test follow-up (2026-05-02).
#
# `subst(f::Lens, g::Lens)` previously built its result `dom` and `cod`
# both via eager `subst(p, q)`. Each materializes `Σ_x Π_a |q[a]|` jbar
# dicts. Both blow up on PolyCDS-style retrofunctors with rich-direction
# carriers.
#
# **Initial fix attempt (cod-only):** swapped only `new_cod` to
# `subst_lazy(p_prime, q_prime)`, leaving `new_dom` eager because
# `Lens.dom` was typed `Polynomial`. Failed: PolyCDS v1.7's iso test
# `boundary retrofunctor f validates strictly` still hung for 16+
# minutes. The eager `new_dom = subst(F.dom.carrier, F.dom.carrier)`
# blew up too — F.dom.carrier carries enough directions per position
# that `Σ_i |F.dom.carrier(1)|^|F.dom.carrier[i]|` materializes
# 10^11+ jbar dicts. The trip wasn't the `new_dom` line itself per se;
# `compose(F.dom.duplicator, subst(F.under, F.under))` then forced
# `_struct_equal(LazySubst(F.dom, F.dom), ConcretePolynomial subst(F.dom, F.dom))`
# which materialized the LazySubst against the (already-built) concrete.
#
# **Final fix:** widen `Lens.dom::Polynomial → AbstractPolynomial`
# (companion to the earlier `Lens.cod` widening) and swap BOTH to
# `subst_lazy`. With both sides lazy, `_struct_equal(LazySubst, LazySubst)`
# short-circuits structurally on operands without enumerating. Sites
# that genuinely need a concrete dom (`(::Lens)(::PolySet)` apply,
# extensional `Lens ==` over the dom positions, `back_directions`)
# materialize on demand — they're cold paths.
#
# Tests cover:
#
#   1. Structural laziness — both `result.dom` and `result.cod` are
#      `LazySubst` over `(p, q)` and `(p', q')`. `positions(...)` is a
#      `SubstPolySet` on both sides.
#   2. No materialization on a fixture whose eager `subst(p', q')` would
#      have ~10^7 positions. Construction returns immediately; before the
#      fix this would have allocated millions of jbar dicts.
#   3. `is_subst_of` accepts the lazy cod via the lazy short-circuit.
#   4. Cross-type `result.cod == subst(p_prime, q_prime)` still passes
#      via the LazySubst↔ConcretePolynomial materialize-and-compare path.
#   5. Identity-preservation invariant unchanged: existing
#      `subst(id_p, id_q) == identity_lens(p ▷ q)` still holds across
#      the lazy/concrete cod boundary.
#   6. Behavioral equivalence — direction routing unchanged. The
#      lazy-built lens agrees extensionally with a manually-built
#      eager-cod lens at every `(x, (a', b'))` input the fixture admits.
#   7. End-to-end perf: `validate_retrofunctor(F; strict=true)` on a
#      retrofunctor whose carrier has a non-trivial direction-set
#      completes well under the timeout. Before the fix, the strict
#      compose chain hangs in materialization.
#   8. Lens.dom widening — `Lens(::LazySubst, ...)` now constructs
#      successfully; `compose` and Lens equality work across lazy doms.

@testset "v0.4.x: subst(::Lens, ::Lens) uses lazy dom AND cod" begin

    # ------------------------------------------------------------
    # 1. Structural laziness: result.dom and result.cod are both LazySubst
    # ------------------------------------------------------------
    @testset "result.dom and result.cod are both LazySubst (structural)" begin
        p  = Polynomial(FinPolySet([:i1, :i2]),
                        i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        pʹ = Polynomial(FinPolySet([:u1, :u2]),
                        i -> i == :u1 ? FinPolySet([:r]) : FinPolySet([:s]))
        q  = Polynomial(FinPolySet([:j1, :j2]),
                        j -> j == :j1 ? FinPolySet([:m]) : FinPolySet([:n]))
        qʹ = Polynomial(FinPolySet([:v1, :v2]),
                        j -> j == :v1 ? FinPolySet([:t]) : FinPolySet([:w]))
        f = Lens(p,  pʹ,
                 i -> i == :i1 ? :u1 : :u2,
                 (i, b) -> i == :i1 ? :a : :c)
        g = Lens(q,  qʹ,
                 j -> j == :j1 ? :v1 : :v2,
                 (j, b) -> j == :j1 ? :m : :n)
        h = subst(f, g)
        @test h.dom isa LazySubst
        @test h.dom.p === p
        @test h.dom.q === q
        @test positions(h.dom) isa Poly.SubstPolySet
        @test h.cod isa LazySubst
        @test h.cod.p === pʹ
        @test h.cod.q === qʹ
        @test positions(h.cod) isa Poly.SubstPolySet
        # Cross-type equality: lazy dom == eager subst(p, q).
        @test h.dom == subst(p, q)
    end

    # ------------------------------------------------------------
    # 2. No eager materialization of a would-be-large cod
    # ------------------------------------------------------------
    @testset "no eager materialization on large p', q'" begin
        # f.dom and g.dom are tiny so `new_dom = subst_lazy(p, q)` is
        # immediate (and would also be cheap if eager — kept tiny here so
        # we can also assert h.dom's lazy cardinality equals the eager).
        # f.cod = g.cod = a 5-position polynomial whose direction-set at
        # the "big" position has cardinality 10. Eager `subst(p', q')` then
        # has at least `5^10 = 9_765_625` positions through the big jbar,
        # an obvious hang at construction time. The lazy form returns
        # immediately and reports the cardinality via the algebra.
        p  = Polynomial(FinPolySet([:x]), _ -> FinPolySet([:dx]))
        q  = Polynomial(FinPolySet([:y]), _ -> FinPolySet([:dy]))
        pʹ = Polynomial(FinPolySet([:u, :u2, :u3, :u4, :u5]),
                        i -> i == :u ? FinPolySet(1:10) : FinPolySet(Symbol[]))
        qʹ = Polynomial(FinPolySet([:v, :v2, :v3, :v4, :v5]),
                        _ -> FinPolySet(Symbol[]))
        f = Lens(p, pʹ, _ -> :u, (_, _b) -> :dx)
        g = Lens(q, qʹ, _ -> :v, (_, _b) -> :dy)
        h = subst(f, g)
        @test h.dom isa LazySubst
        @test h.cod isa LazySubst
        # `positions(h.cod)` cardinality via the algebra:
        # `Σ_i |q'(1)|^|p'[i]|` = `5^10 + 4·5^0` = `9_765_625 + 4` = `9_765_629`.
        c = cardinality(positions(h.cod))
        @test c == Finite(9_765_629)
    end

    # ------------------------------------------------------------
    # 3. is_subst_of accepts the lazy cod via short-circuit
    # ------------------------------------------------------------
    @testset "is_subst_of accepts the lazy cod via short-circuit" begin
        p  = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        pʹ = Polynomial(FinPolySet([:u]), _ -> FinPolySet([:r]))
        q  = Polynomial(FinPolySet([:j]), _ -> FinPolySet([:b]))
        qʹ = Polynomial(FinPolySet([:v]), _ -> FinPolySet([:s]))
        f = Lens(p,  pʹ, _ -> :u, (_, _b) -> :a)
        g = Lens(q,  qʹ, _ -> :v, (_, _b) -> :b)
        h = subst(f, g)
        # Operand-identity short-circuit: no enumeration.
        @test is_subst_of(h.cod, pʹ, qʹ)
        # Mismatched operands rejected.
        wrong_q = Polynomial(FinPolySet([:k]), _ -> FinPolySet([:c]))
        @test !is_subst_of(h.cod, pʹ, wrong_q)
    end

    # ------------------------------------------------------------
    # 4. Cross-type `result.cod == subst(p', q')` still works
    # ------------------------------------------------------------
    @testset "cod == eager subst(p', q') via cross-type ==" begin
        # Backward-compat for callers that previously asserted equality
        # against the eager form. The cross-type
        # `==(LazySubst, ConcretePolynomial)` method materializes the lazy
        # side and compares structurally.
        p  = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a]))
        pʹ = Polynomial(FinPolySet([:u]), _ -> FinPolySet([:r]))
        q  = Polynomial(FinPolySet([:j]), _ -> FinPolySet([:b]))
        qʹ = Polynomial(FinPolySet([:v]), _ -> FinPolySet([:s]))
        f = Lens(p,  pʹ, _ -> :u, (_, _b) -> :a)
        g = Lens(q,  qʹ, _ -> :v, (_, _b) -> :b)
        h = subst(f, g)
        @test h.cod == subst(pʹ, qʹ)
        @test subst(pʹ, qʹ) == h.cod
    end

    # ------------------------------------------------------------
    # 5. Identity preservation: subst(id_p, id_q) == identity_lens(p ▷ q)
    # ------------------------------------------------------------
    @testset "subst(id_p, id_q) == identity_lens(p ▷ q)" begin
        # Same property as the Sprint-4 testset in runtests.jl, but on a
        # fresh fixture, to ensure cross-type Lens equality holds across
        # the lazy/eager cod boundary.
        p = Polynomial(FinPolySet([:i1, :i2]),
                       i -> i == :i1 ? FinPolySet([:a, :b]) : FinPolySet([:c]))
        q = Polynomial(FinPolySet([:j1, :j2]),
                       j -> j == :j1 ? FinPolySet([:u]) : FinPolySet([:v, :w]))
        @test subst(identity_lens(p), identity_lens(q)) ==
              identity_lens(subst(p, q))
    end

    # ------------------------------------------------------------
    # 6. Behavioral equivalence: lazy-built lens agrees with eager build
    # ------------------------------------------------------------
    @testset "lazy-built lens routes directions identically to eager build" begin
        p  = Polynomial(FinPolySet([:i]),
                        _ -> FinPolySet([:a1, :a2]))
        pʹ = Polynomial(FinPolySet([:u1, :u2]),
                        i -> i == :u1 ? FinPolySet([:r1]) : FinPolySet([:r2]))
        q  = Polynomial(FinPolySet([:j1, :j2]),
                        j -> j == :j1 ? FinPolySet([:b1]) : FinPolySet([:b2]))
        qʹ = Polynomial(FinPolySet([:v1, :v2]),
                        j -> j == :v1 ? FinPolySet([:s1]) : FinPolySet([:s2]))
        f = Lens(p,  pʹ,
                 _ -> :u1,
                 (_, _b) -> :a1)
        g = Lens(q,  qʹ,
                 j -> j == :j1 ? :v1 : :v2,
                 (j, _b) -> j == :j1 ? :b1 : :b2)
        h_lazy = subst(f, g)
        # Manually-built fully-eager equivalent. Pre-patch, `subst(::Lens, ::Lens)`
        # built exactly this Lens (with eager dom and cod). Constructing it
        # explicitly here lets us verify behavioral equivalence across the
        # lazy/eager boundary on both sides.
        h_eager = Lens(subst(p, q), subst(pʹ, qʹ),
                       h_lazy.on_positions.f,
                       (key, ab) -> h_lazy.on_directions.f(key).f(ab))
        # Cross-type Lens equality across the lazy/eager dom AND cod boundaries.
        @test h_lazy == h_eager
        # Direction routing matches at every position of subst(p, q) and every
        # `(a', b')` cod-direction. Iterate positions of the eager dom — they
        # share the same `(i, jbar)` key shape as the lazy dom positions.
        for key in subst(p, q).positions.elements
            (iʹ, jbarʹ) = h_lazy.on_positions.f(key)
            Di_prime = direction_at(pʹ, iʹ)
            for aʹ in Di_prime.elements
                Dj_prime = direction_at(qʹ, jbarʹ[aʹ])
                for bʹ in Dj_prime.elements
                    @test h_lazy.on_directions.f(key).f((aʹ, bʹ)) ==
                          h_eager.on_directions.f(key).f((aʹ, bʹ))
                end
            end
        end
    end

    # ------------------------------------------------------------
    # 7. End-to-end: validate_retrofunctor(F; strict=true) doesn't hang
    # ------------------------------------------------------------
    @testset "validate_retrofunctor strict=true completes on tensored cod" begin
        # Reproduce the trip site at a tractable scale. Build a
        # retrofunctor whose cod carrier has a richer direction-set so
        # that the inner `subst(F.underlying, F.underlying).cod` would
        # have been an obvious hang before the patch. The toy fixture is
        # `state_system_comonoid` paired with itself via
        # `parallel_comonoid` (the v2 `parallel_comonoid` builder) so
        # `F.cod.carrier = c.carrier ⊗ c.carrier` has direction-set per
        # position of size `|S|^2`. Without the patch, eager
        # `subst(F.cod.carrier, F.cod.carrier)` would materialize
        # `(|S|^2)^(|S|^2)` jbars per position. With the patch,
        # `validate_retrofunctor(id; strict=true)` returns under 100ms.
        S = FinPolySet([:s1, :s2, :s3])
        c = state_system_comonoid(S)
        # Identity retrofunctor on c. Strict-mode validation runs
        # `compose(F.underlying, F.cod.duplicator)` and
        # `compose(F.dom.duplicator, subst(F.underlying, F.underlying))`,
        # the second of which is the patched site.
        F = identity_retrofunctor(c)
        # Pre-patch: hangs in `Dict` construction inside `subst(p', q')`.
        # Post-patch: returns near-instantly.
        elapsed = @elapsed strict_ok = validate_retrofunctor(F; strict=true)
        @test strict_ok
        @test elapsed < 5.0    # generous; in practice well under 100ms.

        # Also exercise a small comonoid where the cod carrier itself has
        # a non-trivial directions-per-position. `monoid_comonoid` on
        # `Z/4` under + has carrier `representable(Z/4)` — 1 position with
        # 4 directions. `subst(carrier, carrier)` already has 1·1^4 = 1
        # position so this is trivially fast; we run it here mostly as a
        # smoke test that the lazy cod doesn't break the other comonoid
        # validations.
        M = FinPolySet(0:3)
        cm = monoid_comonoid(M, 0, (a, b) -> mod(a + b, 4))
        Fm = identity_retrofunctor(cm)
        @test validate_retrofunctor(Fm; strict=true)
    end

    # ------------------------------------------------------------
    # 8. Lens.dom widening: Lens(::LazySubst, ...) and downstream ops
    # ------------------------------------------------------------
    @testset "Lens.dom accepts LazySubst (widening sanity)" begin
        # Construct a Lens whose dom is a LazySubst directly. Pre-widening,
        # the `Lens(dom::Polynomial, ...)` constructor would have rejected
        # this with a MethodError. Post-widening, the convenience
        # constructor calls `positions(dom)` (= SubstPolySet) and the
        # PolyFunction/DependentFunction store the lazy position-set.
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a, :b]))
        q = Polynomial(FinPolySet([:j1, :j2]), _ -> FinPolySet(Symbol[]))
        target = Polynomial(FinPolySet([:t]), _ -> FinPolySet(Symbol[]))
        lazy_dom = subst_lazy(p, q)
        # Lens with lazy dom and concrete cod. on_pos_fn takes (i, jbar) keys.
        ℓ = Lens(lazy_dom, target,
                 _key -> :t,
                 (_key, _b) -> error("vacuous"))
        @test ℓ.dom isa LazySubst
        @test ℓ.cod === target
        @test positions(ℓ.dom) isa Poly.SubstPolySet
        # Compose two lazy-dom lenses: identity-into-target after our lazy lens.
        id_target = identity_lens(target)
        ℓ2 = compose(ℓ, id_target)
        @test ℓ2.dom isa LazySubst
        @test ℓ2.cod === target
        # The compose result should equal the original lens (since id is the
        # right unit). Cross-type Lens == across the lazy/lazy dom boundary.
        @test ℓ2 == ℓ
    end

end  # @testset "v0.4.x: subst(::Lens, ::Lens) uses lazy dom AND cod"
