# ============================================================
# Extensions v2, PR #4: support / PolyElement (concrete + symbolic)
# ============================================================
#
# Per design doc §4 (Q4.1 wrapper, Q4.2 polynomial-only,
# Q4.3 symbolic included via free_variables, Q4.4 Fairbanks-style support
# = image-of-assignment for polynomial functors).

@testset "Extensions v2, PR #4: support + PolyElement (+ free_variables)" begin

    # ============================================================
    # PolyElement construction + display
    # ============================================================

    @testset "PolyElement construction" begin
        p = Polynomial(FinPolySet([:i1]), _ -> FinPolySet([:a, :b]))
        e = PolyElement(p, :i1, Dict(:a => :x, :b => :y))
        @test e isa PolyElement
        @test e.position === :i1
    end

    @testset "PolyElement show is informative" begin
        p = Polynomial(FinPolySet([:i1]), _ -> FinPolySet([:a]))
        e = PolyElement(p, :i1, Dict(:a => :x))
        s = sprint(show, e)
        @test occursin("PolyElement", s)
        @test occursin("i1", s)
    end

    # ============================================================
    # support — concrete
    # ============================================================

    @testset "support of an injective assignment is the full image" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a, :b, :c]))
        # Injective: each direction maps to a distinct codomain element.
        e = PolyElement(p, :i, Dict(:a => 1, :b => 2, :c => 3))
        s = support(e)
        @test cardinality(s) == Finite(3)
        @test Set(s.elements) == Set([1, 2, 3])
    end

    @testset "support folds duplicates to a smaller set" begin
        # Constant assignment: all directions land at the same value.
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a, :b, :c]))
        e = PolyElement(p, :i, Dict(:a => :v, :b => :v, :c => :v))
        s = support(e)
        @test cardinality(s) == Finite(1)
        @test Set(s.elements) == Set([:v])
    end

    @testset "support of a constant position is empty" begin
        # Constant polynomial: position has no directions, so the
        # assignment has no inputs and the support is empty.
        p = Polynomial(FinPolySet([:c1, :c2]), _ -> FinPolySet(Symbol[]))
        e = PolyElement(p, :c1, Dict{Symbol,Any}())
        s = support(e)
        @test cardinality(s) == Finite(0)
    end

    @testset "support accepts Function-valued assignment" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a, :b]))
        e = PolyElement(p, :i, k -> k == :a ? 1 : 2)
        s = support(e)
        @test Set(s.elements) == Set([1, 2])
    end

    @testset "support accepts PolyFunction-valued assignment" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a, :b]))
        S = FinPolySet([1, 2])
        Xi = direction_at(p, :i)
        pf = PolyFunction(Xi, S, k -> k == :a ? 1 : 2)
        e = PolyElement(p, :i, pf)
        s = support(e)
        @test Set(s.elements) == Set([1, 2])
    end

    @testset "support pair-of-args forwarder agrees with PolyElement form" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a, :b]))
        d = Dict(:a => :x, :b => :y)
        s1 = support(PolyElement(p, :i, d))
        s2 = support(p, :i, d)
        @test Set(s1.elements) == Set(s2.elements)
    end

    # ============================================================
    # free_variables — symbolic
    # ============================================================

    @testset "free_variables on bare SymVar" begin
        p = sympoly(:p)
        @test free_variables(p) == Set([Poly.SymVar(:p, :Polynomial)])
    end

    @testset "free_variables on a sum picks up both sides" begin
        p, q = sympoly(:p), sympoly(:q)
        fv = free_variables(p + q)
        @test Poly.SymVar(:p, :Polynomial) in fv
        @test Poly.SymVar(:q, :Polynomial) in fv
        @test length(fv) == 2
    end

    @testset "free_variables on a parallel/⊗ expression" begin
        p, q = sympoly(:p), sympoly(:q)
        fv = free_variables(parallel(p, q))
        @test length(fv) == 2
    end

    @testset "free_variables on subst expression" begin
        p, q = sympoly(:p), sympoly(:q)
        fv = free_variables(subst(p, q))
        @test length(fv) == 2
    end

    @testset "free_variables ignores literals" begin
        # `sym_zero` is a `SymOp` (not a `SymVar`), so it contributes no
        # free variables. `p + sym_zero` therefore has the same free
        # variables as `p` — just `{p}`.
        p = sympoly(:p)
        e = (p + sym_zero).expr
        fv = free_variables(e)
        @test Poly.SymVar(:p, :Polynomial) in fv
        # No foreign vars sneak in beyond p.
        @test all(v -> v.name === :p, fv)
    end

    @testset "free_variables forwards on SymbolicLens" begin
        p = sympoly(:p)
        L = symlens(:f, dom=p, cod=p)
        fv = free_variables(L)
        @test Poly.SymVar(:f, :Lens) in fv
    end

    # ============================================================
    # Adversarial — concrete
    # ============================================================

    @testset "adversarial — support requires finite p[position]" begin
        # NatSet domain at the position — can't iterate.
        p_nat = Polynomial(FinPolySet([:i]), _ -> NatSet())
        e = PolyElement(p_nat, :i, k -> :v)
        @test_throws Exception support(e)
    end

    @testset "adversarial — heterogeneous codomain values" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a, :b, :c]))
        # Mixed Symbol / Int / String image.
        e = PolyElement(p, :i, Dict(:a => :sym, :b => 42, :c => "str"))
        s = support(e)
        @test cardinality(s) == Finite(3)
        @test Set(s.elements) == Set(Any[:sym, 42, "str"])
    end

    @testset "adversarial — first-occurrence order preserved (deterministic)" begin
        # Image distinct values; verify the .elements Vector order matches
        # the first-occurrence sweep over X[i].
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:k1, :k2, :k3]))
        e = PolyElement(p, :i, Dict(:k1 => :first, :k2 => :second, :k3 => :third))
        s = support(e)
        @test s.elements == Any[:first, :second, :third]
    end

    @testset "adversarial — Dict with extra keys is fine (only X[i] iterated)" begin
        # The assignment Dict can have keys outside X[i] — support only
        # iterates X[i] elements, so extras are ignored.
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a, :b]))
        e = PolyElement(p, :i, Dict(:a => :x, :b => :y, :c => :ignored))
        s = support(e)
        @test Set(s.elements) == Set([:x, :y])
    end

    @testset "adversarial — assignment missing a key errors at first miss" begin
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet([:a, :b]))
        # Missing :b in the Dict.
        e = PolyElement(p, :i, Dict(:a => :x))
        @test_throws KeyError support(e)
    end

    @testset "adversarial — large direction-set handled without OOM" begin
        # 1000-element direction-set, assignment is identity.
        p = Polynomial(FinPolySet([:i]), _ -> FinPolySet(1:1000))
        e = PolyElement(p, :i, k -> k)
        s = support(e)
        @test cardinality(s) == Finite(1000)
    end

    # ============================================================
    # Adversarial — symbolic
    # ============================================================

    @testset "adversarial — free_variables on sym_y / sym_zero / sym_one (sentinels)" begin
        # The sentinel literals shouldn't crash; if they're SymVars with
        # special names, they're returned, not silently dropped.
        for s in (sym_y, sym_zero, sym_one)
            fv = free_variables(s)
            @test fv isa Set
        end
    end

    @testset "adversarial — deeply nested SymOp tree" begin
        # Build a 5-deep nested expression.
        p = sympoly(:p)
        deep = parallel(parallel(parallel(parallel(p, p), p), p), p)
        fv = free_variables(deep)
        @test Poly.SymVar(:p, :Polynomial) in fv
    end

    @testset "adversarial — distinct SymVars with same name but different kind" begin
        # `kind` distinguishes :Polynomial vs :Lens. SymVars with same name
        # but different kind are distinct in the Set.
        v_poly = Poly.SymVar(:f, :Polynomial)
        v_lens = Poly.SymVar(:f, :Lens)
        @test v_poly != v_lens
        # Build a polynomial whose expr is v_poly directly.
        p_with_poly = SymbolicPolynomial(v_poly)
        fv_p = free_variables(p_with_poly)
        @test v_poly in fv_p
        # And a lens via symlens.
        L = symlens(:f, dom=p_with_poly, cod=p_with_poly)
        fv_l = free_variables(L)
        @test v_lens in fv_l
    end

end
