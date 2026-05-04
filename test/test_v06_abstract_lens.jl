# ============================================================
# v0.6 — `AbstractLens` supertype + accessor interface
# ============================================================
#
# Spec: PolyMarkov.jl spin-up (2026-05-03). The supertype is purely
# additive — it gives PolyMarkov's `MarkovLens <: AbstractLens` a
# documented contract to implement, and lets `dom`/`cod`/
# `on_positions`/`on_directions`/`is_deterministic` dispatch
# polymorphically. Method bodies of `compose`, `parallel`, `subst`,
# `*`, `+`, `▷`, `⊙`, etc. remain typed `::Lens` — see
# `docs/dev/abstract_lens.md` for the rationale.

@testset "v0.6 — AbstractLens" begin

    @testset "supertype membership" begin
        @test Lens <: AbstractLens
        @test isabstracttype(AbstractLens)
        f = identity_lens(y)
        @test f isa AbstractLens
        @test f isa Lens
    end

    @testset "accessors return field values (===)" begin
        f = identity_lens(y)
        @test dom(f) === f.dom
        @test cod(f) === f.cod
        @test on_positions(f) === f.on_positions
        @test on_directions(f) === f.on_directions
    end

    @testset "accessors on a non-trivial Lens (discrete_comonoid eraser)" begin
        # 3-element discrete comonoid: carrier = linear({:x, :y_, :z}).
        # Its eraser ε : carrier → y is a Lens; exercise the accessors.
        S = FinPolySet([:x, :y_, :z])
        c = discrete_comonoid(S)
        e = c.eraser
        @test e isa Lens
        @test e isa AbstractLens
        @test dom(e) === e.dom
        @test cod(e) === e.cod
        @test on_positions(e) === e.on_positions
        @test on_directions(e) === e.on_directions
    end

    @testset "is_deterministic on Lens" begin
        @test is_deterministic(identity_lens(y)) === true
        S = FinPolySet([:a, :b])
        c = discrete_comonoid(S)
        @test is_deterministic(c.eraser) === true
        @test is_deterministic(c.duplicator) === true
    end

    @testset "backward-compat — existing constructors still accept Lens" begin
        # Smoke test: the abstract-supertype refactor doesn't break
        # downstream constructors typed `::Lens`. Existing test files
        # cover the deeper backward-compat surface (Comonoid, Retrofunctor,
        # RightComodule, Bicomodule, etc., are exercised throughout the
        # suite).
        S = FinPolySet([:a, :b])
        c = discrete_comonoid(S)
        @test c isa Comonoid
        @test c.eraser isa Lens
        @test c.duplicator isa Lens
    end

end
