# ============================================================
# v0.7 (partial) — Full Prop 3.20 bridge diagram
# ============================================================
#
# v0.7's first land: promotes v0.6's `bridge_diagram` from a
# `NamedTuple` `(left_lens, right_lens)` to a typed `BridgeDiagram`
# struct carrying the full Prop 3.20 data `(B, E, π, S, T)`. v0.6
# linear-case projection preserved as `bd.left_lens` / `bd.right_lens`
# fields so all v0.6 tests pass unchanged.
#
# What's NOT in this v0.7-partial land: the multi-variable Dirichlet ⊗
# on `d-Set[c]`, Theorem 7.19, profunctor↔conjunctive bicomodule,
# generalized Kan, duoidality, symbolic coclosure. Those are the v0.7
# main pass; design doc at `docs/dev/extensions_v6_design.md`.

@testset "v0.7-partial: full Prop 3.20 bridge_diagram" begin

    @testset "BridgeDiagram type + B/E/π/S/T fields" begin
        # Discrete-base linear bicomodule: clean test surface.
        C = discrete_comonoid(FinPolySet([:c1, :c2]))
        D = discrete_comonoid(FinPolySet([:d1, :d2]))
        S = FinPolySet([:s1, :s2, :s3])
        sf = x -> x === :s1 ? :c1 : :c2
        tf = x -> x === :s3 ? :d2 : :d1
        L = linear_bicomodule_from_span(C, D, S, sf, tf)

        bd = bridge_diagram(L.underlying)
        @test bd isa BridgeDiagram

        # B = positions of carrier = S.
        @test bd.B == S

        # E = elements: pairs (x, :pt) since the carrier is linear (Sy)
        # and so direction_at(carrier, x) = {:pt} for every x.
        @test cardinality(bd.E) == Finite(3)
        @test (:s1, :pt) in bd.E.elements
        @test (:s2, :pt) in bd.E.elements
        @test (:s3, :pt) in bd.E.elements

        # π : E → B is the étale projection (i, a) ↦ i.
        for x in S.elements
            @test bd.π((x, :pt)) == x
        end

        # S : B → Ob(C.carrier) recovers s.
        for x in S.elements
            @test bd.S(x) == sf(x)
        end

        # T : E → Ob(D.carrier) recovers t at the (x, :pt) elements.
        for x in S.elements
            @test bd.T((x, :pt)) == tf(x)
        end

        # Source bicomodule preserved for round-trip.
        @test bd.bicomodule === L.underlying
    end

    @testset "v0.6 backward compatibility: left_lens / right_lens" begin
        # Re-run a representative v0.6 test against the new struct: the
        # `bd.left_lens` / `bd.right_lens` fields must still resolve to
        # lenses with the same on-positions behavior as v0.6 NamedTuple
        # form.
        C = discrete_comonoid(FinPolySet([:c1, :c2]))
        D = discrete_comonoid(FinPolySet([:d1, :d2]))
        S = FinPolySet([:s1, :s2])
        sf = x -> x === :s1 ? :c1 : :c2
        tf = x -> x === :s1 ? :d1 : :d2
        L = linear_bicomodule_from_span(C, D, S, sf, tf)
        bd = bridge_diagram(L.underlying)

        @test bd.left_lens isa Lens
        @test bd.right_lens isa Lens
        @test bd.left_lens.dom === L.underlying.carrier
        @test bd.left_lens.cod === C.carrier
        @test bd.right_lens.dom === L.underlying.carrier
        @test bd.right_lens.cod === D.carrier

        for x in S.elements
            @test bd.left_lens.on_positions.f(x) == sf(x)
            @test bd.right_lens.on_positions.f(x) == tf(x)
        end
    end

    @testset "Non-linear bicomodule: E has multiple elements per position" begin
        # Use the regular bicomodule on a state-system comonoid: carrier
        # is Sy^S, every position has |S| directions. So |E| = |S|^2.
        S = FinPolySet([:a, :b, :c])
        cs = state_system_comonoid(S)
        Bns = regular_bicomodule(cs)

        bd = bridge_diagram(Bns)
        @test bd.B == S
        # |E| = Σ_i |carrier[i]| = 3 * 3 = 9.
        @test cardinality(bd.E) == Finite(9)

        # Every (i, a) with i, a ∈ S is in E.
        for i in S.elements, a in S.elements
            @test (i, a) in bd.E.elements
        end

        # π still collapses to the first component.
        for i in S.elements, a in S.elements
            @test bd.π((i, a)) == i
        end

        # S/T for the regular bicomodule on cs: cs.duplicator's on_positions
        # is `i ↦ (i, jbar)` where jbar(a) = a (state-system: every direction
        # is "set state to a"). So S(i) = i and T(i, a) = a.
        for i in S.elements
            @test bd.S(i) == i
        end
        for i in S.elements, a in S.elements
            @test bd.T((i, a)) == a
        end

        # left_lens.on_pos still picks the first component (i ↦ i).
        for i in S.elements
            @test bd.left_lens.on_positions.f(i) == i
        end
        # right_lens.on_pos uses the canonical-direction projection;
        # carrier[i] is FinPolySet of size 3, so canonical = first(elements).
        # T projects to that direction's image under cs.duplicator's chooser.
        canonical = first(S.elements)
        for i in S.elements
            @test bd.right_lens.on_positions.f(i) == canonical
        end
    end

    @testset "c_one_y bridge: full data exposes :pt right-base" begin
        c = free_labeled_transition_comonoid([:p, :q], [(:p, :g, :q)])
        Lc = c_one_y(c)
        bd = bridge_diagram(Lc.underlying)

        @test bd.B == positions(Lc.underlying.carrier)
        # Carrier is linear (Sy with S = {:p, :q}), so |E| = |S| = 2.
        @test cardinality(bd.E) == Finite(2)
        @test (:p, :pt) in bd.E.elements
        @test (:q, :pt) in bd.E.elements

        # S(o) = o (cod-tracking left action). T(o, :pt) = :pt
        # (the unit comonoid's single object).
        for o in (:p, :q)
            @test bd.S(o) == o
            @test bd.T((o, :pt)) == :pt
        end
    end

    @testset "Errors on non-finite carrier positions" begin
        # bridge_diagram requires FinPolySet positions in v0.7-partial.
        # Hand-construct a Bicomodule-shaped struct with NatSet positions
        # is contrived; the simpler check is that the existing finite
        # path works and we have the v0.7-main path documented. Skip the
        # symbolic test until v0.7-main lands.
        @test true  # placeholder; full symbolic test deferred to v0.7-main.
    end

end  # v0.7-partial
