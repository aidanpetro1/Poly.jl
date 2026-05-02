# ============================================================
# Extensions v2, PR #5: comonoid_from_data + bicomodule_from_data
# ============================================================
#
# Authoring helpers that build a `Comonoid` / `Bicomodule` from explicit
# Dicts of coaction / duplicator data, without hand-building the
# underlying Lens objects. Validates by default; `validate=false` skips.

@testset "Extensions v2, PR #5: comonoid_from_data + bicomodule_from_data" begin

    # ============================================================
    # comonoid_from_data
    # ============================================================

    @testset "comonoid_from_data — round-trip via state_system_comonoid" begin
        # Recover the state-system comonoid by extracting its data tables
        # from the existing built-in and rebuilding via comonoid_from_data.
        S = FinPolySet([:a, :b, :c])
        cs = state_system_comonoid(S)
        cat = to_category(cs)

        eraser_table = Dict(s => cat.identity[s][2] for s in S.elements)
        duplicator_emit = Dict((s, a) => cat.cod[(s, a)]
                               for (s, a) in cat.morphisms.elements)
        duplicator_compose = Dict()
        for ((f, g), h) in cat.composition
            (i, a) = f
            (_, b) = g
            duplicator_compose[(i, a, b)] = h[2]
        end

        c = comonoid_from_data(cs.carrier;
                               eraser_table=eraser_table,
                               duplicator_emit=duplicator_emit,
                               duplicator_compose=duplicator_compose)
        @test c isa Comonoid
        @test validate_comonoid(c)
    end

    @testset "comonoid_from_data — discrete category" begin
        S = FinPolySet([:x, :y, :z])
        cd = discrete_comonoid(S)
        cat = to_category(cd)

        eraser_table = Dict(s => cat.identity[s][2] for s in S.elements)
        duplicator_emit = Dict((s, a) => cat.cod[(s, a)]
                               for (s, a) in cat.morphisms.elements)
        duplicator_compose = Dict()
        for ((f, g), h) in cat.composition
            (i, a) = f; (_, b) = g
            duplicator_compose[(i, a, b)] = h[2]
        end

        c = comonoid_from_data(cd.carrier;
                               eraser_table=eraser_table,
                               duplicator_emit=duplicator_emit,
                               duplicator_compose=duplicator_compose)
        @test validate_comonoid(c)
    end

    @testset "comonoid_from_data — validation failure raises ArgumentError" begin
        # Use a deliberately-broken composition table (left-projection
        # in place of monoid op).
        M = FinPolySet(0:2)
        # Build the bad data tables for a Z/3-shaped carrier.
        carrier = representable(M)
        eraser_table = Dict(:pt => 0)
        duplicator_emit = Dict((:pt, a) => :pt for a in M.elements)
        # Bad: composed = first arg (left projection) — not a valid monoid.
        duplicator_compose = Dict((:pt, a, b) => a for a in M.elements
                                                    for b in M.elements)
        @test_throws ArgumentError comonoid_from_data(
            carrier;
            eraser_table=eraser_table,
            duplicator_emit=duplicator_emit,
            duplicator_compose=duplicator_compose)
    end

    @testset "comonoid_from_data — validate=false skips check" begin
        M = FinPolySet(0:2)
        carrier = representable(M)
        eraser_table = Dict(:pt => 0)
        duplicator_emit = Dict((:pt, a) => :pt for a in M.elements)
        duplicator_compose = Dict((:pt, a, b) => a for a in M.elements
                                                    for b in M.elements)
        # Skipping validation: returns a (not-actually-valid) Comonoid object.
        c = comonoid_from_data(carrier;
                               eraser_table=eraser_table,
                               duplicator_emit=duplicator_emit,
                               duplicator_compose=duplicator_compose,
                               validate=false)
        @test c isa Comonoid
        @test !validate_comonoid(c)  # confirms it really is invalid
    end

    # ============================================================
    # bicomodule_from_data
    # ============================================================

    @testset "bicomodule_from_data — round-trip via regular bicomodule" begin
        # Extract data from a regular bicomodule and rebuild via
        # bicomodule_from_data.
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)

        # The regular bicomodule's coactions are both cs.duplicator.
        # Extract its data tables.
        carrier = B.carrier
        cat_S = to_category(cs)

        # Left coaction: x ↦ (x, jbar) since regular_bicomodule routes
        # through the duplicator on both sides.
        left_position_map = Dict()
        right_position_map = Dict()
        for x in carrier.positions.elements
            x_dup, jbar = cs.duplicator.on_positions.f(x)
            left_position_map[x] = (x_dup, jbar)
            right_position_map[x] = jbar
        end

        # Back-direction tables.
        left_back_directions = Dict()
        right_back_directions = Dict()
        for x in carrier.positions.elements
            (lb_pos, jbar_L) = left_position_map[x]
            for b in direction_at(cs.carrier, lb_pos).elements
                a_target_pos = jbar_L[b]
                for a in direction_at(carrier, a_target_pos).elements
                    left_back_directions[(x, b, a)] =
                        cs.duplicator.on_directions.f(x).f((b, a))
                end
            end
            jbar_R = right_position_map[x]
            for a in direction_at(carrier, x).elements
                rb_pos = jbar_R[a]
                for e in direction_at(cs.carrier, rb_pos).elements
                    right_back_directions[(x, a, e)] =
                        cs.duplicator.on_directions.f(x).f((a, e))
                end
            end
        end

        B2 = bicomodule_from_data(
            carrier, cs, cs;
            left_position_map=left_position_map,
            left_back_directions=left_back_directions,
            right_position_map=right_position_map,
            right_back_directions=right_back_directions)
        @test B2 isa Bicomodule
        @test validate_bicomodule(B2)
    end

    @testset "bicomodule_from_data — validation failure raises ArgumentError" begin
        # Tamper with one back-direction entry to fail compatibility.
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        carrier = B.carrier

        left_position_map = Dict()
        right_position_map = Dict()
        for x in carrier.positions.elements
            x_dup, jbar = cs.duplicator.on_positions.f(x)
            left_position_map[x] = (x_dup, jbar)
            right_position_map[x] = jbar
        end
        left_back_directions = Dict()
        right_back_directions = Dict()
        for x in carrier.positions.elements
            (lb_pos, jbar_L) = left_position_map[x]
            for b in direction_at(cs.carrier, lb_pos).elements
                target = jbar_L[b]
                for a in direction_at(carrier, target).elements
                    left_back_directions[(x, b, a)] =
                        cs.duplicator.on_directions.f(x).f((b, a))
                end
            end
            jbar_R = right_position_map[x]
            for a in direction_at(carrier, x).elements
                rb_pos = jbar_R[a]
                for e in direction_at(cs.carrier, rb_pos).elements
                    right_back_directions[(x, a, e)] =
                        cs.duplicator.on_directions.f(x).f((a, e))
                end
            end
        end
        # Lie at one specific (x, b, a) triple to break compatibility.
        first_key = first(keys(left_back_directions))
        existing = left_back_directions[first_key]
        # Pick a different valid direction from the carrier-direction-set.
        x_first = first_key[1]
        all_dirs = direction_at(carrier, x_first).elements
        wrong = first(d for d in all_dirs if d != existing)
        left_back_directions[first_key] = wrong

        @test_throws ArgumentError bicomodule_from_data(
            carrier, cs, cs;
            left_position_map=left_position_map,
            left_back_directions=left_back_directions,
            right_position_map=right_position_map,
            right_back_directions=right_back_directions)
    end

    @testset "bicomodule_from_data — validate=false skips check" begin
        # Same broken setup as above; validate=false returns the bad
        # Bicomodule without raising. Confirms it really is invalid.
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        B = regular_bicomodule(cs)
        carrier = B.carrier

        left_position_map = Dict()
        right_position_map = Dict()
        for x in carrier.positions.elements
            x_dup, jbar = cs.duplicator.on_positions.f(x)
            left_position_map[x] = (x_dup, jbar)
            right_position_map[x] = jbar
        end
        left_back_directions = Dict()
        right_back_directions = Dict()
        for x in carrier.positions.elements
            (lb_pos, jbar_L) = left_position_map[x]
            for b in direction_at(cs.carrier, lb_pos).elements
                target = jbar_L[b]
                for a in direction_at(carrier, target).elements
                    left_back_directions[(x, b, a)] =
                        cs.duplicator.on_directions.f(x).f((b, a))
                end
            end
            jbar_R = right_position_map[x]
            for a in direction_at(carrier, x).elements
                rb_pos = jbar_R[a]
                for e in direction_at(cs.carrier, rb_pos).elements
                    right_back_directions[(x, a, e)] =
                        cs.duplicator.on_directions.f(x).f((a, e))
                end
            end
        end
        first_key = first(keys(left_back_directions))
        existing = left_back_directions[first_key]
        x_first = first_key[1]
        all_dirs = direction_at(carrier, x_first).elements
        wrong = first(d for d in all_dirs if d != existing)
        left_back_directions[first_key] = wrong

        B2 = bicomodule_from_data(
            carrier, cs, cs;
            left_position_map=left_position_map,
            left_back_directions=left_back_directions,
            right_position_map=right_position_map,
            right_back_directions=right_back_directions,
            validate=false)
        @test B2 isa Bicomodule
        @test !validate_bicomodule(B2)
    end

    # ============================================================
    # Adversarial tests
    # ============================================================

    @testset "adversarial — comonoid_from_data missing key raises KeyError" begin
        # If a back-direction or eraser entry is missing, the constructor
        # builds a Lens with a closure that reaches into the Dict; the
        # KeyError surfaces at validation time (when validate=true) or at
        # first call (when validate=false and user invokes a coaction).
        S = FinPolySet([:a, :b])
        cs = state_system_comonoid(S)
        cat = to_category(cs)
        eraser_table = Dict(s => cat.identity[s][2] for s in S.elements)
        duplicator_emit = Dict((s, a) => cat.cod[(s, a)]
                               for (s, a) in cat.morphisms.elements)
        # Intentionally leave duplicator_compose empty.
        duplicator_compose = Dict()
        @test_throws Exception comonoid_from_data(
            cs.carrier;
            eraser_table=eraser_table,
            duplicator_emit=duplicator_emit,
            duplicator_compose=duplicator_compose)
    end

    @testset "adversarial — bicomodule_from_data with empty carrier" begin
        # Empty carrier (no positions) — coaction Dicts can be empty, the
        # bicomodule trivially validates.
        empty_carrier = Polynomial(FinPolySet(Symbol[]),
                                   _ -> FinPolySet(Symbol[]))
        S = FinPolySet([:a])
        cs = state_system_comonoid(S)
        B = bicomodule_from_data(
            empty_carrier, cs, cs;
            left_position_map=Dict(),
            left_back_directions=Dict(),
            right_position_map=Dict(),
            right_back_directions=Dict())
        @test B isa Bicomodule
        @test validate_bicomodule(B)
    end

    @testset "adversarial — comonoid_from_data on singleton trivial comonoid" begin
        # Singleton state-system: |S| = 1, carrier = y. The from_data
        # constructor handles the 1-position case with eraser_table[:lone]
        # = :lone and trivial duplicator data.
        S = FinPolySet([:lone])
        carrier = monomial(S, S)
        eraser_table = Dict(:lone => :lone)
        duplicator_emit = Dict((:lone, :lone) => :lone)
        duplicator_compose = Dict((:lone, :lone, :lone) => :lone)
        c = comonoid_from_data(carrier;
                               eraser_table=eraser_table,
                               duplicator_emit=duplicator_emit,
                               duplicator_compose=duplicator_compose)
        @test validate_comonoid(c)
    end

    @testset "adversarial — comonoid_from_data with discrete + monoid cross-shape" begin
        # Build a manual product: two-object discrete-like comonoid with
        # an explicit identity-only structure on each object.
        S = FinPolySet([:x, :y])
        carrier = linear(S)   # one direction per position (a singleton :pt)
        eraser_table = Dict(:x => :pt, :y => :pt)
        duplicator_emit = Dict((:x, :pt) => :x, (:y, :pt) => :y)
        duplicator_compose = Dict((:x, :pt, :pt) => :pt,
                                  (:y, :pt, :pt) => :pt)
        c = comonoid_from_data(carrier;
                               eraser_table=eraser_table,
                               duplicator_emit=duplicator_emit,
                               duplicator_compose=duplicator_compose)
        @test validate_comonoid(c)
        @test cardinality(to_category(c).objects) == Finite(2)
        @test cardinality(to_category(c).morphisms) == Finite(2)  # only identities
    end

end
