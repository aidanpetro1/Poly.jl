# ============================================================
# v0.4 #1: symbolic non-identity D for kan_2cat
# ============================================================
#
# v0.3.x errored on `kan_2cat(D, F)` when carriers had non-FinPolySet
# positions. v0.4 emits a structural KanExtension whose `extension`
# bicomodule has `SymbolicCoequalizer` positions and `SymbolicSet`
# direction-sets. The unit/counit BicomoduleMorphism has placeholder
# on_positions / on_directions that error if called on concrete
# elements (symbolic results are structural; evaluation requires
# carrier specialization).
#
# Coverage:
#
#   1. SymbolicCoequalizer construction, cardinality, equality.
#   2. kan_2cat with symbolic D + concrete F: returns a KanExtension,
#      no error.
#   3. The extension carrier's positions are a SymbolicCoequalizer.
#   4. Unit is a BicomoduleMorphism (typecheck only).
#   5. Identity-D regression: still works for finite carriers.
#   6. Both directions :left and :right.
#   7. factor_through on symbolic extension returns a BicomoduleMorphism.
#   8. Calling the symbolic unit's on_positions errors (placeholder).

@testset "v0.4 #1: symbolic non-identity D for kan_2cat" begin

    @testset "SymbolicCoequalizer basics" begin
        parent = SymbolicSet(:Q)
        empty_relation = Tuple{Any,Any}[]
        coeq = SymbolicCoequalizer(parent, empty_relation)
        @test coeq isa Poly.PolySet
        @test coeq isa SymbolicCoequalizer
        @test coeq.parent === parent
        @test coeq.relation == empty_relation
        # cardinality is symbolic (default-derived from parent).
        @test cardinality(coeq) isa Poly.SymbolicCardinality
    end

    @testset "SymbolicCoequalizer with explicit cardinality" begin
        parent = SymbolicSet(:R)
        coeq = SymbolicCoequalizer(parent, Tuple{Any,Any}[]; cardinality=Finite(7))
        @test cardinality(coeq) == Finite(7)
    end

    @testset "SymbolicCoequalizer equality" begin
        parent = SymbolicSet(:S)
        c1 = SymbolicCoequalizer(parent, Tuple{Any,Any}[(:a, :b)])
        c2 = SymbolicCoequalizer(parent, Tuple{Any,Any}[(:a, :b)])
        c3 = SymbolicCoequalizer(parent, Tuple{Any,Any}[(:c, :d)])
        @test c1 == c2
        @test c1 != c3
        @test hash(c1) == hash(c2)
    end

    # ============================================================
    # kan_2cat dispatch — identity D regression first
    # ============================================================

    @testset "identity D regression: still returns F unchanged" begin
        cs = state_system_comonoid(FinPolySet([:s1, :s2]))
        F = regular_bicomodule(cs)
        # Identity D = regular_bicomodule(cs).
        D = regular_bicomodule(cs)
        k_left  = kan_2cat(D, F; direction=:left)
        k_right = kan_2cat(D, F; direction=:right)
        @test k_left.extension === F
        @test k_right.extension === F
    end

    # ============================================================
    # Symbolic non-identity D: carriers are SymbolicSet
    # ============================================================

    @testset "kan_2cat with symbolic carrier on D returns KanExtension" begin
        # Build a symbolic D and F. We construct a Bicomodule with
        # SymbolicSet-positioned carrier; the bicomodule constructor's
        # is_subst_of check passes via the LazySubst short-circuit when
        # coactions use subst_lazy codomains.
        cs = state_system_comonoid(FinPolySet([:s1, :s2]))
        cs_other = state_system_comonoid(FinPolySet([:t1, :t2]))

        sym_pos = SymbolicSet(:Q_sym)
        sym_carrier = Polynomial(sym_pos, _ -> SymbolicSet(:Q_sym_dir))

        # Placeholder coaction functions that error if invoked.
        _err = (args...) -> error("symbolic carrier coaction not invokable")

        D_carrier_left  = Lens(sym_carrier, Poly.subst_lazy(cs.carrier, sym_carrier),
                               _err, _err)
        D_carrier_right = Lens(sym_carrier, Poly.subst_lazy(sym_carrier, cs_other.carrier),
                               _err, _err)
        D = Bicomodule(sym_carrier, cs, cs_other, D_carrier_left, D_carrier_right)

        # F shares the same source comonoid as D (= cs).
        F = regular_bicomodule(cs)

        # Non-identity D check (D.left_base !== D.right_base) — succeeds.
        @test D.left_base !== D.right_base

        # kan_2cat must not error and must return a KanExtension.
        k_left = kan_2cat(D, F; direction=:left)
        @test k_left isa Poly.KanExtension
        @test k_left.direction === :left
        # Extension carrier positions are a SymbolicCoequalizer.
        @test k_left.extension.carrier.positions isa SymbolicCoequalizer

        k_right = kan_2cat(D, F; direction=:right)
        @test k_right isa Poly.KanExtension
        @test k_right.direction === :right
        @test k_right.extension.carrier.positions isa SymbolicCoequalizer
    end

    @testset "symbolic kan_2cat unit is a BicomoduleMorphism (typecheck only)" begin
        cs = state_system_comonoid(FinPolySet([:s1, :s2]))
        cs_other = state_system_comonoid(FinPolySet([:t1, :t2]))
        sym_pos = SymbolicSet(:Q_sym2)
        sym_carrier = Polynomial(sym_pos, _ -> SymbolicSet(:Q_sym2_dir))
        _err = (args...) -> error("symbolic carrier coaction not invokable")
        D_left  = Lens(sym_carrier, Poly.subst_lazy(cs.carrier, sym_carrier), _err, _err)
        D_right = Lens(sym_carrier, Poly.subst_lazy(sym_carrier, cs_other.carrier), _err, _err)
        D = Bicomodule(sym_carrier, cs, cs_other, D_left, D_right)
        F = regular_bicomodule(cs)

        k = kan_2cat(D, F; direction=:left)
        @test k.unit isa Poly.BicomoduleMorphism
        # Unit's target is the extension. Its source is a stub-bases-rewrap
        # of F (because BicomoduleMorphism requires source/target share
        # bases by `===`, and the extension's bases generally differ from
        # F's). We check the structural properties rather than `=== F`.
        @test k.unit.target === k.extension
        @test k.unit.source.carrier === F.carrier
        @test k.unit.source.left_base === k.extension.left_base
        @test k.unit.source.right_base === k.extension.right_base
    end

    @testset "factor_through on symbolic extension" begin
        cs = state_system_comonoid(FinPolySet([:s1, :s2]))
        cs_other = state_system_comonoid(FinPolySet([:t1, :t2]))
        sym_pos = SymbolicSet(:Q_sym3)
        sym_carrier = Polynomial(sym_pos, _ -> SymbolicSet(:Q_sym3_dir))
        _err = (args...) -> error("symbolic carrier coaction not invokable")
        D_left  = Lens(sym_carrier, Poly.subst_lazy(cs.carrier, sym_carrier), _err, _err)
        D_right = Lens(sym_carrier, Poly.subst_lazy(sym_carrier, cs_other.carrier), _err, _err)
        D = Bicomodule(sym_carrier, cs, cs_other, D_left, D_right)
        F = regular_bicomodule(cs)

        k_left = kan_2cat(D, F; direction=:left)
        # A test α : F ⇒ F (identity 2-cell). For a left Kan factoring, the
        # source of α should be k.input.
        α = identity_bicomodule_morphism(F)
        # Build a concrete α by an identity to make typing trivial.
        # factor_through must not error on the symbolic extension path.
        β = factor_through(k_left, α)
        @test β isa Poly.BicomoduleMorphism
        @test β.source === k_left.extension
    end

    @testset "symbolic unit's on_positions errors when invoked" begin
        # The placeholder lens errors with a clear message if you try
        # to evaluate it at a concrete position.
        cs = state_system_comonoid(FinPolySet([:s1, :s2]))
        cs_other = state_system_comonoid(FinPolySet([:t1, :t2]))
        sym_pos = SymbolicSet(:Q_sym4)
        sym_carrier = Polynomial(sym_pos, _ -> SymbolicSet(:Q_sym4_dir))
        _err = (args...) -> error("symbolic carrier coaction not invokable")
        D_left  = Lens(sym_carrier, Poly.subst_lazy(cs.carrier, sym_carrier), _err, _err)
        D_right = Lens(sym_carrier, Poly.subst_lazy(sym_carrier, cs_other.carrier), _err, _err)
        D = Bicomodule(sym_carrier, cs, cs_other, D_left, D_right)
        F = regular_bicomodule(cs)

        k = kan_2cat(D, F; direction=:left)
        # Calling the unit's underlying on_positions at any element should error.
        @test_throws ErrorException k.unit.underlying.on_positions.f(:any_element)
    end
end
