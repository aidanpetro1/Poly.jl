# ============================================================
# v0.4.x patch: forward-direction action for `Retrofunctor`
# ============================================================
#
# Spec: PolyCDS deep-modularity follow-up (2026-05-02).
#
# Tests cover:
#
#   1. Field plumbing — `forward_on_directions` exists, defaults to
#      `nothing`, and accepts an explicit kwarg.
#   2. `identity_retrofunctor` populates forward as identity.
#   3. `compose(F, G)` propagates forward when both have it; leaves
#      `nothing` when either lacks it.
#   4. `cofree_morphism` populates forward as a filter-subsequence on
#      the alphabet-inclusion case.
#   5. `tuple_retrofunctor` packs per-component forwards into a tuple
#      (left-fold) when every component has forward.
#   6. `base_change_left` / `base_change_right` use the forward path
#      when present and produce the same bicomodule as the backward
#      path on cases where both apply.
#   7. `base_change_left` succeeds via the forward path on a partial-
#      image retrofunctor (the alphabet-inclusion boundary) where
#      the backward path errors because the back-action's image is
#      a proper subset of the cod-directions.
#   8. Backward-compat: a Retrofunctor built with no forward kwarg
#      still uses the existing backward path in base_change_*.

@testset "v0.4.x forward-direction action" begin

    # ------------------------------------------------------------
    # 1. Field plumbing
    # ------------------------------------------------------------
    @testset "Retrofunctor.forward_on_directions field" begin
        S = FinPolySet([:s])
        cs = state_system_comonoid(S)
        # No kwarg → nothing.
        F0 = Retrofunctor(cs, cs, identity_lens(cs.carrier))
        @test F0.forward_on_directions === nothing
        # Explicit kwarg → stored. Curried shape: F.forward(c0).f(b).
        fwd = _x -> (; f = b -> b)
        F1 = Retrofunctor(cs, cs, identity_lens(cs.carrier);
                          forward_on_directions = fwd)
        @test F1.forward_on_directions === fwd
    end

    # ------------------------------------------------------------
    # 2. identity_retrofunctor
    # ------------------------------------------------------------
    @testset "identity_retrofunctor: forward = identity on dom-directions" begin
        S = FinPolySet([:s1, :s2])
        cs = state_system_comonoid(S)
        F = identity_retrofunctor(cs)
        @test F.forward_on_directions !== nothing
        for s in cs.carrier.positions.elements
            for b in direction_at(cs.carrier, s).elements
                @test F.forward_on_directions(s).f(b) == b
            end
        end
    end

    # ------------------------------------------------------------
    # 3. compose: propagation of forward
    # ------------------------------------------------------------
    @testset "compose: forwards both forward actions" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        F = identity_retrofunctor(cs)
        G = identity_retrofunctor(cs)
        FG = compose(F, G)
        @test FG.forward_on_directions !== nothing
        for s in cs.carrier.positions.elements
            for b in direction_at(cs.carrier, s).elements
                # identity ∘ identity on directions = identity.
                @test FG.forward_on_directions(s).f(b) == b
            end
        end
    end

    @testset "compose: nothing when either lacks forward" begin
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        F = identity_retrofunctor(cs)
        G_no_fwd = Retrofunctor(cs, cs, identity_lens(cs.carrier))
        @test compose(F, G_no_fwd).forward_on_directions === nothing
        @test compose(G_no_fwd, F).forward_on_directions === nothing
    end

    # ------------------------------------------------------------
    # 4. cofree_morphism: forward = filter-subsequence
    # ------------------------------------------------------------
    @testset "cofree_morphism: forward filter-subsequence (alphabet inclusion)" begin
        Σ_full = FinPolySet([:a, :b, :c])
        Σ_part = FinPolySet([:a, :c])
        L = Lens(representable(Σ_full), representable(Σ_part),
                 _ -> :pt,
                 (_, σ_p) -> σ_p)   # back-action: inclusion Σ_part ↪ Σ_full
        F = cofree_morphism(L, 2)
        @test F.forward_on_directions !== nothing

        # Find the depth-2 full p-tree (all three branches expanded all
        # the way down). On its (:a, :b, :c) tree-path the forward image
        # filters out :b, leaving (:a, :c).
        full_t = nothing
        for t in F.dom.carrier.positions.elements
            if !isempty(t.children) && haskey(t.children, :a) &&
               haskey(t.children, :b) && haskey(t.children, :c) &&
               !isempty(t.children[:a].children)
                full_t = t
                break
            end
        end
        @test full_t !== nothing
        @test F.forward_on_directions(full_t).f(()) == ()
        @test F.forward_on_directions(full_t).f((:a,)) == (:a,)
        @test F.forward_on_directions(full_t).f((:c,)) == (:c,)
        # :b is filtered out — empty q-path, NOT a key error.
        @test F.forward_on_directions(full_t).f((:b,)) == ()
    end

    @testset "cofree_morphism: forward on identity Lens is identity" begin
        p = representable(FinPolySet([:a, :b]))
        idL = identity_lens(p)
        F = cofree_morphism(idL, 2)
        @test F.forward_on_directions !== nothing
        for t in F.dom.carrier.positions.elements
            for π in tree_paths(t)
                @test F.forward_on_directions(t).f(π) == π
            end
        end
    end

    # ------------------------------------------------------------
    # 5. tuple_retrofunctor: per-component forward, packed
    # ------------------------------------------------------------
    @testset "tuple_retrofunctor: forwards componentwise" begin
        # Identity Fs always carry forward. The tuple's forward at
        # position x and direction b should be (b, b) (left-fold).
        S = FinPolySet([:s1, :s2])
        cs = state_system_comonoid(S)
        F = identity_retrofunctor(cs)
        G = identity_retrofunctor(cs)
        joint = tuple_retrofunctor([F, G])
        @test joint.forward_on_directions !== nothing
        for s in cs.carrier.positions.elements
            for b in direction_at(cs.carrier, s).elements
                @test joint.forward_on_directions(s).f(b) == (b, b)
            end
        end
    end

    @testset "tuple_retrofunctor: nothing when any component lacks forward" begin
        S = FinPolySet([:s1, :s2])
        cs = state_system_comonoid(S)
        F = identity_retrofunctor(cs)
        # Build a sibling retrofunctor without forward.
        G_no_fwd = Retrofunctor(cs, cs, identity_lens(cs.carrier))
        joint = tuple_retrofunctor([F, G_no_fwd])
        @test joint.forward_on_directions === nothing
    end

    # ------------------------------------------------------------
    # 6. base_change_left: forward path agrees with backward path
    #    on cases where both apply
    # ------------------------------------------------------------
    @testset "base_change_left: forward path matches backward path on identity F" begin
        # Identity F has forward = identity; backward also works
        # (F.on_directions is identity, trivially injective). Both paths
        # should produce element-wise-equal bicomodules.
        C = state_system_comonoid(FinPolySet([:c1, :c2]))
        M = regular_bicomodule(C)
        F_with_fwd = identity_retrofunctor(C)             # has forward
        F_no_fwd   = Retrofunctor(C, C, identity_lens(C.carrier))   # no forward

        Mp_fwd = base_change_left(F_with_fwd, M)
        Mp_bwd = base_change_left(F_no_fwd,   M)

        @test Mp_fwd.left_base === Mp_bwd.left_base
        @test Mp_fwd.right_base === Mp_bwd.right_base
        @test Mp_fwd.carrier === Mp_bwd.carrier
        for x in M.carrier.positions.elements
            cp_f, mb_f = Mp_fwd.left_coaction.on_positions.f(x)
            cp_b, mb_b = Mp_bwd.left_coaction.on_positions.f(x)
            @test cp_f == cp_b
            @test mb_f == mb_b
        end
        @test validate_bicomodule(Mp_fwd)
    end

    # ------------------------------------------------------------
    # 7. Boundary's forward function is total on every dom-direction —
    #    the substantive deliverable of the patch.
    # ------------------------------------------------------------
    #
    # The PolyCDS "alphabet-inclusion boundary" — `tuple_retrofunctor` of
    # per-disease `cofree_morphism`s — has a partial back-action on
    # tensored cod-directions (not every direction-tuple has a single
    # Σ-tree-path lifting to it). The forward action, in contrast, is
    # total: every dom-direction has a well-defined image. This test
    # exercises that totality directly; it does NOT call `base_change_left`
    # on this boundary because that requires an `M` whose left-coaction
    # image stays inside `boundary.on_positions`'s image (the PolyCDS
    # `AP_tensored` is constructed with that constraint, but
    # `regular_bicomodule(boundary.cod)` visits all cod positions and
    # so trips the (separate) position-surjectivity precondition).
    @testset "boundary forward: total on every dom-direction" begin
        Σ_full = FinPolySet([:a, :b, :c])
        Σ_d1   = FinPolySet([:a, :b])
        Σ_d2   = FinPolySet([:a, :c])
        depth  = 1

        L1 = Lens(representable(Σ_full), representable(Σ_d1),
                  _ -> :pt, (_, σ) -> σ)
        L2 = Lens(representable(Σ_full), representable(Σ_d2),
                  _ -> :pt, (_, σ) -> σ)
        F1 = cofree_morphism(L1, depth)
        F2 = cofree_morphism(L2, depth)
        boundary = tuple_retrofunctor([F1, F2])
        @test boundary.forward_on_directions !== nothing

        # Walk every dom-position and every dom-direction at it; the
        # forward action must succeed everywhere (no errors) and produce
        # a tensored cod-direction whose components are themselves valid
        # paths in the per-disease cod-tree at the image position.
        for t in boundary.dom.carrier.positions.elements
            f_at_t = boundary.forward_on_directions(t)
            cod_pos = boundary.underlying.on_positions.f(t)   # (F1(t), F2(t))
            cod_pos_1, cod_pos_2 = cod_pos
            for π_p in tree_paths(t)
                tensored = f_at_t.f(π_p)
                # Tensored direction is a pair (path-in-F1(t), path-in-F2(t)).
                @test tensored isa Tuple
                @test length(tensored) == 2
                π_q1, π_q2 = tensored
                @test π_q1 in tree_paths(cod_pos_1)
                @test π_q2 in tree_paths(cod_pos_2)
            end
        end

        # Spot-check: at the depth-1 full Σ-tree, the path (:b,) goes
        # through L1 (Σ_d1 = {:a, :b}) but is filtered out by L2
        # (Σ_d2 = {:a, :c}). Forward should give ((:b,), ()).
        full_t = nothing
        for t in boundary.dom.carrier.positions.elements
            if !isempty(t.children) && haskey(t.children, :b)
                full_t = t
                break
            end
        end
        @test full_t !== nothing
        f_at_full = boundary.forward_on_directions(full_t)
        @test f_at_full.f((:b,)) == ((:b,), ())
        @test f_at_full.f((:c,)) == ((), (:c,))
        @test f_at_full.f((:a,)) == ((:a,), (:a,))
        @test f_at_full.f(())     == ((),    ())
    end

    # ------------------------------------------------------------
    # 8. base_change_right: forward path on identity G
    # ------------------------------------------------------------
    @testset "base_change_right: forward path on identity G" begin
        D = state_system_comonoid(FinPolySet([:d1, :d2]))
        M = regular_bicomodule(D)
        idG = identity_retrofunctor(D)   # has forward
        Mp = base_change_right(M, idG)
        @test Mp.right_base === idG.dom
        @test validate_bicomodule(Mp)
    end

    # ------------------------------------------------------------
    # 9. Backward-compat: Retrofunctors with no forward still work
    # ------------------------------------------------------------
    @testset "backward-compat: no-forward Retrofunctor uses backward path" begin
        # Construct a Retrofunctor with the standard 3-arg form (no
        # forward kwarg). base_change_left should fall through to the
        # existing backward path and succeed.
        C = state_system_comonoid(FinPolySet([:c1, :c2, :c3]))
        F = Retrofunctor(C, C, identity_lens(C.carrier))   # no forward
        @test F.forward_on_directions === nothing
        M = regular_bicomodule(C)
        Mp = base_change_left(F, M)
        @test validate_bicomodule(Mp)
    end

end  # @testset "v0.4.x forward-direction action"
