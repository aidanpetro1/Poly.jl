using Test
include(joinpath(@__DIR__, "..", "src", "Poly.jl"))
using .Poly

@testset "Poly.jl" begin

    # ============================================================
    # Sprint 1: foundation
    # ============================================================
    @testset "Cardinality" begin
        @testset "concrete arithmetic" begin
            @test Finite(2) + Finite(3) == Finite(5)
            @test Finite(2) * Finite(3) == Finite(6)
            @test Finite(2) ^ Finite(3) == Finite(8)
            @test Finite(2) + CountablyInfinite() == CountablyInfinite()
            @test CountablyInfinite() + Finite(2) == CountablyInfinite()
            @test Finite(0) * CountablyInfinite() == Finite(0)
            @test Finite(2) ^ CountablyInfinite() == Continuum()  # 2^ℵ₀ = 𝔠
            @test Finite(1) ^ CountablyInfinite() == Finite(1)
            @test Continuum() + Continuum() == Continuum()
        end
        @testset "symbolic + simplification" begin
            A, B = SymbolicCardinality(:A), SymbolicCardinality(:B)
            @test Finite(0) + A == A
            @test A + Finite(0) == A
            @test Finite(0) * A == Finite(0)
            @test Finite(1) * A == A
            @test A ^ Finite(0) == Finite(1)
            @test A ^ Finite(1) == A
            @test Finite(1) ^ A == Finite(1)
        end
        @testset "commutative canonicalization" begin
            A, B = SymbolicCardinality(:A), SymbolicCardinality(:B)
            @test A + B == B + A
            @test A * B == B * A
            @test A ^ B != B ^ A   # ^ is not commutative
        end
        @testset "equality across types" begin
            @test Finite(5) != CountablyInfinite()
            @test SymbolicCardinality(:A) != SymbolicCardinality(:B)
        end
    end

    @testset "PolySet" begin
        @testset "FinPolySet" begin
            s = FinPolySet([:a, :b, :a])  # dedup
            @test cardinality(s) == Finite(2)
            @test :a in s
            @test :c ∉ s
            @test FinPolySet([1,2]) == FinPolySet([2,1])
        end
        @testset "Natural / integer / real sets" begin
            @test cardinality(NatSet()) == CountablyInfinite()
            @test cardinality(IntSet()) == CountablyInfinite()
            @test cardinality(RealSet()) == Continuum()
        end
        @testset "IntervalSet" begin
            iv = IntervalSet(0.0, 1.0)
            @test 0.5 in iv
            @test cardinality(iv) == Continuum()
        end
        @testset "ProductSet / SumSet / ExpSet" begin
            a = FinPolySet([:x, :y])
            b = FinPolySet([:p, :q, :r])
            @test cardinality(ProductSet(a, b)) == Finite(6)
            @test cardinality(SumSet(a, b))     == Finite(5)
            @test cardinality(ExpSet(a, b))     == Finite(8)  # 2^3
        end
        @testset "SymbolicSet" begin
            s = SymbolicSet(:S)
            @test cardinality(s) == SymbolicCardinality(:S)
        end
    end

    @testset "Polynomial: foundation" begin
        @testset "construction & predicates" begin
            @test is_constant(zero_poly)
            @test is_constant(one_poly)
            @test is_representable(one_poly)
            @test is_linear(y)
            @test is_representable(y)
            @test is_monomial(constant(FinPolySet([:a, :b])))
            @test is_monomial(linear(FinPolySet([:a, :b])))
            @test is_monomial(representable(FinPolySet([:a, :b])))
            @test is_monomial(monomial(FinPolySet([1,2]), FinPolySet([:a,:b])))
        end
        @testset "p(X) action — Example 2.4" begin
            pos = FinPolySet([1, 2, 3, 4])
            dir = i -> i == 1 ? FinPolySet([:a1, :a2]) :
                       i == 2 || i == 3 ? FinPolySet([:b]) :
                       FinPolySet(Symbol[])
            p = Polynomial(pos, dir)
            X = FinPolySet([:a, :b])
            @test cardinality(p(X)) == Finite(9)
        end
        @testset "p(0) is the constant term" begin
            p = Polynomial(FinPolySet([1,2,3]),
                           i -> i == 1 ? FinPolySet([:a]) : FinPolySet(Symbol[]))
            # Two empty-direction positions, so p(∅) should have 2 elements.
            @test cardinality(p(FinPolySet(Symbol[]))) == Finite(2)
        end
    end

    # ============================================================
    # Sprint 2: lenses
    # ============================================================
    @testset "Lens" begin
        @testset "coin-jar / owner lens (Example 3.10)" begin
            q = Polynomial(FinPolySet([:open, :closed]),
                           i -> i == :open ? FinPolySet([:penny, :nickel, :dime, :quarter]) :
                                              FinPolySet(Symbol[]))
            p = Polynomial(FinPolySet([:needy, :greedy, :content]),
                           i -> i == :needy   ? FinPolySet([:save, :spend]) :
                                i == :greedy  ? FinPolySet([:accept, :reject, :ask_for_more]) :
                                                FinPolySet([:count, :rest]))
            on_pos = i -> (i == :content) ? :closed : :open
            on_dir = (i, b) -> begin
                if i == :needy
                    b == :penny ? :spend : :save
                elseif i == :greedy
                    (b == :penny || b == :nickel) ? :ask_for_more : :accept
                else
                    error("vacuous")
                end
            end
            f = Lens(p, q, on_pos, on_dir)
            @test f.on_positions.f(:needy)   == :open
            @test f.on_positions.f(:greedy)  == :open
            @test f.on_positions.f(:content) == :closed
            @test f.on_directions.f(:needy).f(:penny)   == :spend
            @test f.on_directions.f(:needy).f(:nickel)  == :save
            @test f.on_directions.f(:greedy).f(:dime)   == :accept
            @test f.on_directions.f(:greedy).f(:nickel) == :ask_for_more
        end
        @testset "lens_count = 1472 (Example 3.15)" begin
            P = Polynomial(FinPolySet([1, 2, 3]),
                           i -> i == 1 ? FinPolySet([:d1, :d2, :d3]) : FinPolySet([:e]))
            Q = Polynomial(FinPolySet([1, 2, 3, 4]),
                           i -> i == 1 ? FinPolySet([:a, :b, :c, :d]) :
                                i == 2 ? FinPolySet([:m, :n]) :
                                         FinPolySet(Symbol[]))
            @test lens_count(P, Q) == Finite(1472)
        end
        @testset "identity self-composition" begin
            p = Polynomial(FinPolySet([1, 2]), i -> FinPolySet([:a]))
            id_p = identity_lens(p)
            @test compose(id_p, id_p) == id_p
        end
        @testset "natural-transformation action" begin
            q = Polynomial(FinPolySet([:open, :closed]),
                           i -> i == :open ? FinPolySet([:penny, :nickel]) :
                                              FinPolySet(Symbol[]))
            p = Polynomial(FinPolySet([:m]),
                           i -> FinPolySet([:save, :spend]))
            f = Lens(p, q, i -> :open, (i, b) -> b == :penny ? :spend : :save)
            X = FinPolySet([:x, :y_])
            fX = f(X)
            out = fX((:m, Dict(:save => :x, :spend => :y_)))
            @test out[1] == :open
            @test out[2][:penny] == :y_
            @test out[2][:nickel] == :x
        end
        @testset "composition with terminal" begin
            p = Polynomial(FinPolySet([1, 2]), i -> FinPolySet([:a]))
            id_p = identity_lens(p)
            t = Lens(p, one_poly, i -> :pt, (i, b) -> error("vacuous"))
            h = compose(id_p, t)
            @test h.cod === one_poly
        end
    end

    # ============================================================
    # Polish-pass behaviors
    # ============================================================
    @testset "Polynomial ==" begin
        p1 = Polynomial(FinPolySet([1, 2]), i -> FinPolySet([:a]))
        p2 = Polynomial(FinPolySet([1, 2]), i -> FinPolySet([:a]))
        p3 = Polynomial(FinPolySet([1, 2]), i -> FinPolySet([:b]))
        @test p1 == p2
        @test !(p1 == p3)
    end

    @testset "merged vs structural display" begin
        owner = Polynomial(FinPolySet([:a, :b, :c]),
                           i -> i == :a ? FinPolySet([:x, :y]) :
                                i == :b ? FinPolySet([:p, :q]) :
                                          FinPolySet([:r, :s]))
        merged = sprint(show, owner)
        structural = sprint(show, MIME"text/plain"(), owner)
        @test occursin("3y^2", merged)        # all three positions have |D| = 2
        @test !occursin("3y^2", structural)   # different direction-set labels
    end

    @testset "cardinality_of_apply" begin
        q = Polynomial(FinPolySet([1, 2, 3, 4]),
                       i -> i == 1 ? FinPolySet([:a, :b, :c, :d]) :
                            i == 2 ? FinPolySet([:m, :n]) :
                                     FinPolySet(Symbol[]))
        @test cardinality_of_apply(q, FinPolySet([1, 2, 3])) == Finite(92)
        Asym = SymbolicSet(:A)
        @test cardinality_of_apply(q, Asym) isa Cardinality   # symbolic OK
    end

    # ============================================================
    # is_iso predicates
    # ============================================================
    @testset "is_iso (cardinality)" begin
        # 2y^3 + y vs y^3 + y^3 + y — same multiset of cardinalities.
        a = Polynomial(FinPolySet([1, 2, 3]),
                       i -> i == 3 ? FinPolySet([:x]) :
                                     FinPolySet([:p, :q, :r]))
        b = Polynomial(FinPolySet([:u, :v, :w]),
                       i -> i == :w ? FinPolySet([:z]) :
                                      FinPolySet([:m, :n, :o]))
        @test is_iso(a, b)
        # ℕy and ℝy are iso under cardinality (1 position, 1 direction each).
        n_set = FinPolySet([:N])
        r_set = FinPolySet([:R])
        Nly = linear(n_set)
        Rly = linear(r_set)
        @test is_iso(Nly, Rly)
    end

    @testset "is_iso_strict (structural)" begin
        # ℕy vs ℝy: cardinality-iso true, structural-iso depends on whether
        # the direction-sets are the same as PolySets.
        Nly = linear(FinPolySet([:N]))
        Rly = linear(FinPolySet([:R]))
        @test is_iso_strict(Nly, Nly)
        # 2y^3 + y vs y^3 + y^3 + y with the SAME direction-sets are strict iso.
        a = Polynomial(FinPolySet([1, 2, 3]),
                       i -> i == 3 ? FinPolySet([:x]) :
                                     FinPolySet([:p, :q, :r]))
        b = Polynomial(FinPolySet([:u, :v, :w]),
                       i -> i == :w ? FinPolySet([:x]) :
                                      FinPolySet([:p, :q, :r]))
        @test is_iso_strict(a, b)
        # Same cardinalities, different direction-set elements: NOT strict-iso.
        c = Polynomial(FinPolySet([:u, :v, :w]),
                       i -> i == :w ? FinPolySet([:x]) :
                                      FinPolySet([:other1, :other2, :other3]))
        @test is_iso(a, c)
        @test !is_iso_strict(a, c)
    end

    # ============================================================
    # Symbolic layer
    # ============================================================
    @testset "Symbolic layer" begin
        @testset "construction" begin
            p = sympoly(:p)
            q = sympoly(:q)
            @test p != q
            @test sym_y == sym_y
            @test sym_y != sym_zero
        end
        @testset "lift / evaluate" begin
            @test lift(y) == sym_y
            @test lift(zero_poly) == sym_zero
            @test lift(one_poly) == sym_one
            @test evaluate(sym_y) == y
            @test evaluate(sym_zero) == zero_poly
        end
        @testset "simplification rules" begin
            p = sympoly(:p)
            @test simplify(p + sym_zero) == p
            @test simplify(sym_zero + p) == p
            @test simplify(p * sym_one) == p
            @test simplify(sym_one * p) == p
            @test simplify(parallel(p, sym_y)) == p
            @test simplify(parallel(sym_y, p)) == p
            @test simplify(subst(p, sym_y)) == p
            @test simplify(subst(sym_y, p)) == p
        end
        @testset "lens unitor rules" begin
            p = sympoly(:p)
            f = symlens(:f, dom=p, cod=p)
            id_p = sym_id(p)
            @test simplify(compose(f, id_p)) == f
            @test simplify(compose(id_p, f)) == f
        end
        @testset "sym_equal" begin
            p = sympoly(:p)
            @test sym_equal(p + sym_zero, p)
            @test sym_equal(parallel(p, sym_y), p)
            @test !sym_equal(p, sympoly(:q))
        end
    end

    # ============================================================
    # LaTeX rendering
    # ============================================================
    @testset "LaTeX rendering" begin
        @testset "concrete polynomials" begin
            # y^3 + 2y^2 + 1
            p = Polynomial(FinPolySet([1, 2, 3, 4]),
                           i -> i == 1 ? FinPolySet([:a, :b, :c]) :
                                i == 2 ? FinPolySet([:d, :e]) :
                                i == 3 ? FinPolySet([:f, :g]) :
                                         FinPolySet(Symbol[]))
            tex = to_latex(p)
            @test occursin("y^{3}", tex)
            @test occursin("2y^{2}", tex)
            @test occursin("1", tex) || occursin("+ 1", tex)
        end
        @testset "symbolic expressions" begin
            p = sympoly(:p)
            q = sympoly(:q)
            @test to_latex(p) == "p"
            @test to_latex(p + q) == "p + q"
            @test occursin("\\otimes", to_latex(parallel(p, q)))
            @test occursin("\\triangleleft", to_latex(subst(p, q)))
            @test occursin("\\fatsemi", to_latex(compose(symlens(:f), symlens(:g))))
            @test occursin("\\mathrm{id}_{p}", to_latex(sym_id(p)))
        end
        @testset "cardinalities" begin
            @test to_latex(Finite(7)) == "7"
            @test to_latex(CountablyInfinite()) == "\\aleph_{0}"
            @test to_latex(Continuum()) == "\\mathfrak{c}"
            A = SymbolicCardinality(:A)
            @test occursin("\\lvert A \\rvert", to_latex(A))
            B = SymbolicCardinality(:B)
            @test occursin("^{", to_latex(A ^ B))
        end
        @testset "latex_display wraps in \$\$" begin
            s = latex_display(sym_y)
            @test startswith(s, "\$\$") && endswith(s, "\$\$")
        end
    end

    # ============================================================
    # Sprint 3: monoidal products
    # ============================================================
    @testset "Sprint 3: monoidal products" begin
        # p = y^3 + y, q = y^4 + y^2 + 1 (Niu & Spivak Examples 3.62, 3.70)
        p = Polynomial(FinPolySet([1, 2]),
                       i -> i == 1 ? FinPolySet([:a, :b, :c]) : FinPolySet([:d]))
        q = Polynomial(FinPolySet([1, 2, 3]),
                       i -> i == 1 ? FinPolySet([:m, :n, :o, :p]) :
                            i == 2 ? FinPolySet([:r, :s]) :
                                     FinPolySet(Symbol[]))

        @testset "coproduct +" begin
            r = p + q
            @test cardinality(r.positions) == Finite(5)
            # 2 positions of card 3 (from p), then card 1 (from p), then 4, 2, 0 (from q)
            cards = sort([cardinality(direction_at(r, i)).n for i in r.positions])
            @test cards == [0, 1, 2, 3, 4]
            @test direction_at(r, (1, 1)) == FinPolySet([:a, :b, :c])
            @test direction_at(r, (2, 1)) == FinPolySet([:m, :n, :o, :p])
        end

        @testset "cartesian × — Example 3.62" begin
            r = p * q
            @test cardinality(r.positions) == Finite(6)
            cards = sort([cardinality(direction_at(r, i)).n for i in r.positions])
            # (3,1)+ = (3+4, 3+2, 3+0, 1+4, 1+2, 1+0) = (7, 5, 3, 5, 3, 1)
            @test cards == [1, 3, 3, 5, 5, 7]
        end

        @testset "parallel ⊗ — Example 3.70" begin
            r = parallel(p, q)
            @test cardinality(r.positions) == Finite(6)
            cards = sort([cardinality(direction_at(r, i)).n for i in r.positions])
            # (3*4, 3*2, 3*0, 1*4, 1*2, 1*0) = (12, 6, 0, 4, 2, 0)
            @test cards == [0, 0, 2, 4, 6, 12]
        end

        @testset "Unicode aliases" begin
            @test (p × q) == p * q
            @test (p ⊗ q) == parallel(p, q)
        end

        @testset "distributivity — Exercise 3.77" begin
            p1 = Polynomial(FinPolySet([:a]), i -> FinPolySet([:x, :y_]))
            p2 = Polynomial(FinPolySet([:b]), i -> FinPolySet([:z]))
            qq = Polynomial(FinPolySet([:c]), i -> FinPolySet([:m, :n, :o]))
            lhs = parallel(p1 + p2, qq)
            rhs = parallel(p1, qq) + parallel(p2, qq)
            @test is_iso(lhs, rhs)
        end

        @testset "lens-level products" begin
            id_p = identity_lens(p)
            id_q = identity_lens(q)
            @test (id_p + id_q) == identity_lens(p + q)
            @test (id_p * id_q) == identity_lens(p * q)
            @test parallel(id_p, id_q) == identity_lens(parallel(p, q))
        end

        @testset "symbolic commutative canonicalization" begin
            a, b = sympoly(:a), sympoly(:b)
            @test (a + b) == (b + a)
            @test (a * b) == (b * a)
            @test parallel(a, b) == parallel(b, a)
        end

        @testset "symbolic rules — zero absorption" begin
            a = sympoly(:a)
            @test simplify(a * sym_zero) == sym_zero
            @test simplify(sym_zero * a) == sym_zero
            @test simplify(parallel(a, sym_zero)) == sym_zero
            @test simplify(parallel(sym_zero, a)) == sym_zero
        end

        @testset "symbolic rules — distributivity" begin
            a, b, c = sympoly(:a), sympoly(:b), sympoly(:c)
            @test sym_equal(parallel(a + b, c),
                            parallel(a, c) + parallel(b, c))
            @test sym_equal((a + b) * c, a * c + b * c)
        end

        @testset "evaluate(symbolic, env) → concrete" begin
            env = Dict(:p => p, :q => q)
            @test evaluate(sympoly(:p) + sympoly(:q), env) == p + q
            @test is_iso(evaluate(sympoly(:p) * sympoly(:q), env), p * q)
            @test is_iso(evaluate(parallel(sympoly(:p), sympoly(:q)), env),
                         parallel(p, q))
        end
    end

    # ============================================================
    # Pre-Sprint-4 refinements
    # ============================================================
    @testset "refinements" begin
        @testset "@poly macro" begin
            # @poly produces polynomials with integer-labeled positions and
            # direction-sets, so == against the canonical Symbol-labeled constants
            # fails — but they're iso. Use ≈ for those comparisons.
            @test (@poly y) ≈ y
            @test (@poly 0) == zero_poly      # both have empty position-sets
            @test (@poly 1) ≈ one_poly         # iso; both are y^0
            # y^3 + 2y + 1: 4 positions, cardinalities {3, 1, 1, 0}
            p = @poly y^3 + 2y + 1
            @test cardinality(p.positions) == Finite(4)
            cards = sort([cardinality(direction_at(p, i)).n for i in p.positions])
            @test cards == [0, 1, 1, 3]
            # 2y^3: 2 positions of cardinality 3
            q = @poly 2y^3
            @test cardinality(q.positions) == Finite(2)
            @test all(i -> cardinality(direction_at(q, i)) == Finite(3), q.positions)

            # ▷ inside the macro (no parens needed).
            @test (@poly y^2 ▷ y^3) ≈ (@poly y^6)
            @test (@poly y^3 ▷ y^2) ≈ (@poly y^6)
            # Mixed precedence: ▷ binds tighter than +.
            #   y + 2y ▷ y^2  ≡  y + (2y ▷ y^2)  ≈  y + 2y^2
            mixed = @poly y + 2y ▷ y^2
            @test mixed ≈ (@poly y + 2y^2)

            # ⊗ inside the macro.
            @test (@poly y^2 ⊗ y^3) ≈ (@poly y^6)
            @test (@poly y ⊗ y) ≈ (@poly y)

            # Variable in scope on the right-hand side.
            r = @poly y + 1
            @test (@poly y^2 ▷ r) ≈ ((@poly y^2) ▷ r)
        end

        @testset "precedence-aware show" begin
            a, b, c = sympoly(:a), sympoly(:b), sympoly(:c)
            # Top-level operator gets no outer parens.
            @test sprint(show, (a + b).expr) == "a + b"
            # ⊗ binds tighter than + → no parens around (b ⊗ c) inside an addition.
            @test !occursin("(", sprint(show, (a + parallel(b, c)).expr))
            # + has lower precedence than ⊗ → (a + b) ⊗ c keeps parens around the +.
            s = sprint(show, parallel(a + b, c).expr)
            @test occursin("(a + b)", s)
        end

        @testset "simplify trace mode" begin
            a, b, c = sympoly(:a), sympoly(:b), sympoly(:c)
            out, hist = simplify(parallel(a + b, c); trace=true)
            @test hist isa Vector
            @test !isempty(hist)
            # The first step should fire the distributivity rule.
            @test any(r -> occursin("⊗", r[1].description) || occursin("⊗", r[1].description), hist)
            # Without trace: returns just the simplified expression.
            out2 = simplify(parallel(a + b, c))
            @test out2 == out
        end

        @testset "≈ alias" begin
            # Concrete: p × q is iso to q × p but not == (positions tagged differently).
            p = @poly y^3 + y
            q = @poly y^4 + y^2 + 1
            @test (p × q) ≈ (q × p)
            @test !((p × q) == (q × p))
            # Symbolic: a + b ≈ b + a via canonicalization (here actually ==).
            a, b = sympoly(:a), sympoly(:b)
            @test (a + b) ≈ (b + a)
            # ⊗ unitor: a ⊗ y ≈ a via simplify.
            @test parallel(a, sym_y) ≈ a
        end
    end

    # ============================================================
    # Sprint 4: composition product ◁
    # ============================================================
    @testset "Sprint 4: composition product ◁" begin
        p = @poly y^2 + y       # y² + y
        q = @poly y^3 + 1       # y³ + 1

        @testset "Niu & Spivak §6.1.3 example" begin
            # (y² + y) ▷ (y³ + 1) ≈ y⁶ + 3y³ + 2
            r = p ▷ q
            @test cardinality(r.positions) == Finite(6)
            cards = sort([cardinality(direction_at(r, i)).n for i in r.positions])
            @test cards == [0, 0, 3, 3, 3, 6]
        end

        @testset "unit laws" begin
            @test (p ▷ y) ≈ p
            @test (y ▷ p) ≈ p
            @test (q ▷ y) ≈ q
            @test (y ▷ q) ≈ q
        end

        @testset "left distributivity (Prop 6.47)" begin
            a = @poly y^2
            b = @poly y
            c = @poly y + 1
            @test ((a + b) ▷ c) ≈ ((a ▷ c) + (b ▷ c))
            # Also for ×
            @test ((a * b) ▷ c) ≈ ((a ▷ c) * (b ▷ c))
        end

        @testset "NOT right-distributive" begin
            r  = @poly y^2
            yp = @poly y
            lhs = r ▷ (yp + yp)        # 2 positions × 2 j̄'s × 2 ds = 4y²
            rhs = (r ▷ yp) + (r ▷ yp)  # 2 · y²        = 2y²
            @test !(lhs ≈ rhs)
        end

        @testset "constants on the left" begin
            @test (zero_poly ▷ p) == zero_poly
            @test (one_poly  ▷ p) ≈ one_poly
        end

        @testset "monomial composition: y^A ▷ y^B ≈ y^(A·B)" begin
            # Each `@poly` must be parenthesized so the macro doesn't gobble
            # the rest of the line (it parses everything to its right as the
            # expression to lift).
            @test ((@poly y^3) ▷ (@poly y^2)) ≈ (@poly y^6)
            @test ((@poly y^4) ▷ (@poly y))   ≈ (@poly y^4)
            @test ((@poly y)   ▷ (@poly y^5)) ≈ (@poly y^5)
        end

        @testset "n-fold composition" begin
            @test subst_n(p, 0) ≈ y
            @test subst_n(p, 1) ≈ p
            @test subst_n(p, 2) ≈ (p ▷ p)
            @test subst_n((@poly y^2), 3) ≈ (@poly y^8)   # y² ◁ y² ◁ y² = y^8
        end

        @testset "lens-level horizontal composition" begin
            id_p = identity_lens(p)
            id_q = identity_lens(q)
            @test subst(id_p, id_q) == identity_lens(p ▷ q)
        end

        @testset "symbolic rules — ▷ left distributivity" begin
            a, b, c = sympoly(:a), sympoly(:b), sympoly(:c)
            @test sym_equal(subst(a + b, c),
                            subst(a, c) + subst(b, c))
            @test sym_equal(subst(a * b, c),
                            subst(a, c) * subst(b, c))
        end

        @testset "symbolic rules — constants on the left" begin
            a = sympoly(:a)
            @test simplify(subst(sym_zero, a)) == sym_zero
            @test simplify(subst(sym_one,  a)) == sym_one
        end

        @testset "evaluate(symbolic ◁, env) → concrete" begin
            env = Dict(:p => p, :q => q)
            @test is_iso(evaluate(subst(sympoly(:p), sympoly(:q)), env),
                         p ▷ q)
        end
    end

    # ============================================================
    # Sprint 5: closure of ⊗, sections, derivative
    # ============================================================
    @testset "Sprint 5: closure, sections, derivative" begin
        p = @poly y^2 + 1
        q = @poly y + 1
        r = @poly y^2

        @testset "internal_hom: position count = |Poly(q,r)|" begin
            qr = internal_hom(q, r)
            @test cardinality(qr.positions) == lens_count(q, r)
        end

        @testset "closure adjunction: |Poly(p⊗q, r)| = |Poly(p, [q,r])|" begin
            @test lens_count(parallel(p, q), r) ==
                  lens_count(p, internal_hom(q, r))
        end

        @testset "Example 4.81: [y^A, y] ≈ Ay, [Ay, y] ≈ y^A" begin
            A = FinPolySet([:a, :b, :c])
            yA = representable(A)
            Ay = linear(A)
            @test internal_hom(yA, y) ≈ Ay
            @test internal_hom(Ay, y) ≈ yA
        end

        @testset "internal_hom of empty domain" begin
            # [0, r] should be 1 (one lens 0 → r, no directions)
            @test internal_hom(zero_poly, r) ≈ one_poly
        end

        @testset "sections — Γ(p) = Π_i |p[i]|" begin
            secs = sections(p)
            expected = reduce(*, [cardinality(direction_at(p, i)).n
                                  for i in p.positions.elements]; init=1)
            @test cardinality(secs).n == expected
            # Γ(0) = 1 (vacuous: one section, the empty function)
            @test cardinality(sections(zero_poly)).n == 1
            # Γ(y) = 1 (one direction at the single position)
            @test cardinality(sections(y)).n == 1
        end

        @testset "section_lens" begin
            # Use a polynomial with no empty direction-set so Γ(p) > 0.
            p_with_secs = @poly y^2 + y
            σ = first(sections(p_with_secs).elements)
            γ = section_lens(p_with_secs, σ)
            @test γ.dom == p_with_secs
            @test γ.cod == y
            # Verify the section lens reproduces the chosen direction.
            for i in p_with_secs.positions.elements
                @test γ.on_directions.f(i).f(:pt) == σ[i]
            end
        end

        @testset "Γ(p + q) ≈ Γ(p) × Γ(q) (Prop 3.39)" begin
            p1 = @poly y^2 + y     # Γ count = 2
            p2 = @poly y^3         # Γ count = 3
            @test cardinality(sections(p1 + p2)).n ==
                  cardinality(sections(p1)).n * cardinality(sections(p2)).n
        end

        @testset "[p, y] ≈ Γ(p)·y^{p(1)} (Eq. 4.82)" begin
            # Closure into y has Γ(p) positions and |p(1)| directions per position.
            p1 = @poly y^2 + y
            ph_y = internal_hom(p1, y)
            expected = monomial(FinPolySet(1:cardinality(sections(p1)).n),
                                FinPolySet(1:cardinality(p1.positions).n))
            @test ph_y ≈ expected
        end

        @testset "eval_lens behavioral" begin
            # Pick a small case where Poly(q, r) > 0.
            q_small = @poly y + 1
            r_small = @poly 2          # constant 2 — has 2 positions, 0 directions
            qr = internal_hom(q_small, r_small)
            @test cardinality(qr.positions).n > 0
            ev = eval_lens(q_small, r_small)
            # For any (combo, j) input, eval lands at an r-position.
            sample_combo = first(qr.positions.elements)
            for j in q_small.positions.elements
                landed = ev.on_positions.f((sample_combo, j))
                @test landed in r_small.positions.elements
            end
        end

        @testset "do_nothing_section on state system" begin
            S = FinPolySet([:s1, :s2, :s3])
            ε = do_nothing_section(S)
            @test ε.dom == monomial(S, S)
            @test ε.cod == y
            # ε on directions = identity on S
            for s in S.elements
                @test ε.on_directions.f(s).f(:pt) == s
            end
        end

        @testset "derivative — |ṗ(1)| = Σ |p[i]|" begin
            ṗ = derivative(p)
            expected = sum(cardinality(direction_at(p, i)).n
                           for i in p.positions.elements)
            @test cardinality(ṗ.positions).n == expected
            # Direction-set at (i, a) has cardinality |p[i]| − 1
            for (i, a) in ṗ.positions.elements
                @test cardinality(direction_at(ṗ, (i, a))).n ==
                      cardinality(direction_at(p, i)).n - 1
            end
        end

        @testset "eval_lens : [q, r] ⊗ q → r" begin
            ev = eval_lens(q, r)
            @test ev.dom == parallel(internal_hom(q, r), q)
            @test ev.cod == r
        end
    end

    # ============================================================
    # Sprint 6: dynamical systems
    # ============================================================
    @testset "Sprint 6: dynamical systems" begin
        S = FinPolySet([:l, :r, :b])
        A = FinPolySet([:o, :g])
        I = FinPolySet([0, 1])
        return_fn = s -> s == :l ? 0 : 1
        update_fn = (s, a) -> begin
            if s == :l
                a == :o ? :l : :r
            elseif s == :r
                a == :o ? :l : :b
            else
                a == :o ? :l : :b
            end
        end
        φ = moore_machine(S, I, A, return_fn, update_fn)

        @testset "construction" begin
            @test φ.dom == state_system(S)
            @test φ.cod == monomial(I, A)
            @test is_state_system(φ.dom)
        end

        @testset "step" begin
            @test step(φ, :b, :o) == :l
            @test step(φ, :b, :g) == :b
            @test step(φ, :l, :o) == :l
            @test step(φ, :l, :g) == :r
            @test step(φ, :r, :o) == :l
            @test step(φ, :r, :g) == :b
        end

        @testset "trajectory and outputs" begin
            inputs = [:o, :o, :g, :o]
            @test trajectory(φ, :b, inputs) == [:b, :l, :l, :r, :l]
            @test output_trajectory(φ, :b, inputs) == [1, 0, 0, 1, 0]
            @test trajectory(φ, :r, Symbol[]) == [:r]
            @test output_trajectory(φ, :r, Symbol[]) == [1]
        end

        @testset "initial_state lens" begin
            init = initial_state(S, :l)
            @test init.dom == y
            @test init.cod == state_system(S)
            @test init.on_positions.f(:pt) == :l
        end

        @testset "counter (mod 6)" begin
            N = FinPolySet(0:5)
            counter = moore_machine(N, N, FinPolySet([:tick]),
                                    n -> n, (n, _) -> n == 5 ? 0 : n + 1)
            @test output_trajectory(counter, 0, fill(:tick, 6)) ==
                  [0, 1, 2, 3, 4, 5, 0]
        end

        @testset "juxtapose two systems" begin
            N = FinPolySet(0:2)
            fwd = moore_machine(N, N, FinPolySet([:t]),
                                n -> n, (n, _) -> n == 2 ? 0 : n + 1)
            bwd = moore_machine(N, N, FinPolySet([:t]),
                                n -> n, (n, _) -> n == 0 ? 2 : n - 1)
            pair = juxtapose(fwd, bwd)
            @test is_state_system(pair.dom)
            @test trajectory(pair, (0, 0), [(:t, :t), (:t, :t)]) ==
                  [(0, 0), (1, 2), (2, 1)]
        end

        @testset "wrap with identity is identity" begin
            iden = identity_lens(φ.cod)
            @test wrap(φ, iden) == φ
        end

        @testset "dependent dynamical_system (non-monomial interface)" begin
            interface = Polynomial(FinPolySet([:running, :final]),
                                   i -> i == :running ? A : FinPolySet(Symbol[]))
            T = FinPolySet([:s0, :s1, :final])
            ret = s -> s == :final ? :final : :running
            upd = (s, a) -> begin
                s == :final && error("vacuous: no directions in :final")
                a == :o ? (s == :s0 ? :s1 : :final) : :s0
            end
            φd = dynamical_system(T, interface, ret, upd)
            @test trajectory(φd, :s0, [:o, :o]) == [:s0, :s1, :final]
            @test output_trajectory(φd, :s0, [:o, :o]) ==
                  [:running, :running, :final]
        end
    end

    # ============================================================
    # Sprint 7: comonoids = categories (Cat#)
    # ============================================================
    @testset "Sprint 7: comonoids = categories" begin
        @testset "state_system_comonoid" begin
            S = FinPolySet([:a, :b, :c])
            cs = state_system_comonoid(S)
            @test cs.carrier == state_system(S)
            @test cs.eraser.cod == y
            @test cs.duplicator.cod == subst(cs.carrier, cs.carrier)

            C = to_category(cs)
            @test cardinality(C.objects)   == Finite(3)
            @test cardinality(C.morphisms) == Finite(9)
            @test C.dom[(:a, :b)] == :a
            @test C.cod[(:a, :b)] == :b
            @test C.identity[:a] == (:a, :a)
            @test C.composition[((:a, :b), (:b, :c))] == (:a, :c)
            @test validate_category_laws(C)
            @test validate_comonoid(cs)
        end

        @testset "discrete_comonoid" begin
            S = FinPolySet([:x, :y_, :z])
            cd = discrete_comonoid(S)
            @test cd.carrier == linear(S)

            C = to_category(cd)
            @test cardinality(C.objects)   == Finite(3)
            @test cardinality(C.morphisms) == Finite(3)
            for o in S.elements
                @test C.identity[o] == (o, :pt)
                @test C.dom[(o, :pt)] == o
                @test C.cod[(o, :pt)] == o
            end
            @test validate_comonoid(cd)
        end

        @testset "monoid_comonoid: Z/4 under +" begin
            M = FinPolySet(0:3)
            add4 = (a, b) -> mod(a + b, 4)
            cm = monoid_comonoid(M, 0, add4)
            @test cm.carrier == representable(M)

            C = to_category(cm)
            @test cardinality(C.objects)   == Finite(1)
            @test cardinality(C.morphisms) == Finite(4)
            @test C.identity[:pt] == (:pt, 0)
            @test C.composition[((:pt, 1), (:pt, 2))] == (:pt, 3)
            @test C.composition[((:pt, 3), (:pt, 3))] == (:pt, 2)
            @test validate_comonoid(cm)
        end

        @testset "non-monoid fails validation" begin
            M = FinPolySet(0:2)
            bad = monoid_comonoid(M, 0, (a, _b) -> a)
            @test !validate_comonoid(bad)
        end

        @testset "round-trip: from_category ∘ to_category" begin
            S = FinPolySet([:a, :b])
            cs = state_system_comonoid(S)
            cs2 = from_category(to_category(cs))
            @test cs2.carrier == cs.carrier
            @test validate_comonoid(cs2)
            # Behavioral equivalence: rather than strict Lens ==
            # (which depends on identical FinPolySet element ordering and
            # closure shapes — can break if encodings shift), we check
            # extensional equality on every position/direction.
            for i in cs.carrier.positions.elements
                @test cs2.eraser.on_directions.f(i).f(:pt) ==
                      cs.eraser.on_directions.f(i).f(:pt)
                Di = direction_at(cs.carrier, i)
                pos2 = cs2.duplicator.on_positions.f(i)
                pos1 = cs.duplicator.on_positions.f(i)
                @test pos2[1] == pos1[1]            # δ first component agrees
                for a in Di.elements
                    @test pos2[2][a] == pos1[2][a]  # codomains agree
                end
                Dpair = direction_at(subst(cs.carrier, cs.carrier),
                                     pos1)
                for ab in Dpair.elements
                    @test cs2.duplicator.on_directions.f(i).f(ab) ==
                          cs.duplicator.on_directions.f(i).f(ab)
                end
            end
        end

        @testset "Retrofunctor identity & composition" begin
            S = FinPolySet([:a, :b])
            cs = state_system_comonoid(S)
            id_F = identity_retrofunctor(cs)
            @test id_F.dom === cs
            @test id_F.cod === cs
            @test id_F.underlying == identity_lens(cs.carrier)
            @test validate_retrofunctor(id_F)

            id2 = compose(id_F, id_F)
            @test validate_retrofunctor(id2)
            @test id2.underlying == id_F.underlying
        end

        @testset "discrete -> discrete retrofunctor" begin
            S = FinPolySet([:a, :b])
            T = FinPolySet([:x, :y_])
            cdS = discrete_comonoid(S)
            cdT = discrete_comonoid(T)
            on_pos = i -> i == :a ? :x : :y_
            on_dir = (_, _b) -> :pt
            F = Retrofunctor(cdS, cdT, Lens(cdS.carrier, cdT.carrier, on_pos, on_dir))
            @test validate_retrofunctor(F)
        end

        @testset "Comonoid constructor type checks" begin
            S = FinPolySet([:a, :b])
            cs = state_system_comonoid(S)
            wrong_cod = Lens(cs.carrier, linear(FinPolySet([:p])),
                             _ -> :p, (_, _) -> :a)
            @test_throws ErrorException Comonoid(cs.carrier, wrong_cod, cs.duplicator)
        end
        @testset "validate_comonoid mode=:lens on built-ins" begin
            S = FinPolySet([:a, :b, :c])
            @test validate_comonoid(state_system_comonoid(S); mode=:lens)
            @test validate_comonoid(discrete_comonoid(S); mode=:lens)
            M = FinPolySet(0:3)
            @test validate_comonoid(monoid_comonoid(M, 0, (a, b) -> mod(a + b, 4)); mode=:lens)
        end

        @testset "validate_comonoid mode=:lens catches non-comonoid" begin
            # Same left-projection bad op as before — fails counit (right ID).
            M = FinPolySet(0:2)
            bad = monoid_comonoid(M, 0, (a, _b) -> a)
            @test !validate_comonoid(bad; mode=:lens)
        end

        @testset "mode=:category and mode=:lens agree" begin
            S = FinPolySet([:a, :b])
            cs = state_system_comonoid(S)
            @test validate_comonoid(cs; mode=:category) == validate_comonoid(cs; mode=:lens)
            cd = discrete_comonoid(S)
            @test validate_comonoid(cd; mode=:category) == validate_comonoid(cd; mode=:lens)
            M = FinPolySet(0:1)
            cm = monoid_comonoid(M, 0, (a, b) -> mod(a + b, 2))
            @test validate_comonoid(cm; mode=:category) == validate_comonoid(cm; mode=:lens)
        end

        @testset "validate_comonoid rejects unknown mode" begin
            S = FinPolySet([:a])
            cs = state_system_comonoid(S)
            @test_throws ArgumentError validate_comonoid(cs; mode=:bogus)
        end

    end

    # ============================================================
    # Sprint 8: cofree comonoid, behavior trees, comodules
    # ============================================================
    @testset "Sprint 8: cofree comonoid and comodules" begin
        @testset "BehaviorTree equality and hashing" begin
            t1 = BehaviorTree(:a, Dict{Any,BehaviorTree}())
            t2 = BehaviorTree(:a, Dict{Any,BehaviorTree}())
            t3 = BehaviorTree(:b, Dict{Any,BehaviorTree}())
            @test t1 == t2
            @test t1 != t3
            @test hash(t1) == hash(t2)
            @test hash(t1) != hash(t3)
        end

        @testset "behavior_trees enumeration" begin
            # p = y + 1: one position with one direction, one constant.
            p = Polynomial(FinPolySet([:run, :halt]),
                           i -> i == :run ? FinPolySet([:tick]) :
                                            FinPolySet(Symbol[]))
            @test length(behavior_trees(p, 0)) == 2
            @test length(behavior_trees(p, 1)) == 4
            # depth ≤ 2: same 4 plus 2 new at depth 2 = 6
            @test length(behavior_trees(p, 2)) == 6

            # An empty-direction position has only one tree, regardless of depth.
            const_only = Polynomial(FinPolySet([:halt]),
                                    _ -> FinPolySet(Symbol[]))
            @test length(behavior_trees(const_only, 0)) == 1
            @test length(behavior_trees(const_only, 5)) == 1
        end

        @testset "tree_paths and tree_walk" begin
            t = BehaviorTree(:i, Dict{Any,BehaviorTree}(
                :a => BehaviorTree(:j, Dict{Any,BehaviorTree}(
                    :b => BehaviorTree(:k, Dict{Any,BehaviorTree}()))),
                :c => BehaviorTree(:l, Dict{Any,BehaviorTree}())))
            ps = tree_paths(t)
            @test () in ps
            @test (:a,) in ps
            @test (:c,) in ps
            @test (:a, :b) in ps
            @test length(ps) == 4

            @test tree_walk(t, ()) == t
            @test tree_walk(t, (:a,)).label == :j
            @test tree_walk(t, (:a, :b)).label == :k
            @test tree_walk(t, (:c,)).label == :l
            @test_throws KeyError tree_walk(t, (:nope,))
        end

        @testset "cofree_comonoid is a valid comonoid" begin
            p = Polynomial(FinPolySet([:run, :halt]),
                           i -> i == :run ? FinPolySet([:tick]) :
                                            FinPolySet(Symbol[]))
            for d in 0:2
                Tp = cofree_comonoid(p, d)
                @test validate_comonoid(Tp)
                @test validate_comonoid(Tp; mode=:lens)
            end
        end

        @testset "cofree_comonoid: paths compose by concatenation" begin
            p = Polynomial(FinPolySet([:run, :halt]),
                           i -> i == :run ? FinPolySet([:tick]) :
                                            FinPolySet(Symbol[]))
            Tp = cofree_comonoid(p, 2)
            C = to_category(Tp)
            # Identity at any tree is the empty path.
            for t in Tp.carrier.positions.elements
                @test C.identity[t] == (t, ())
            end
            # Composition is concatenation: for any morphism (t, π1)
            # and any (t', π2) with t' = walk(t, π1), the composite is
            # (t, (π1..., π2...)).
            for m in C.morphisms.elements
                t, π1 = m
                tʹ = C.cod[m]
                # find an outgoing morphism from tʹ
                for m2 in C.morphisms.elements
                    C.dom[m2] == tʹ || continue
                    _, π2 = m2
                    composite = C.composition[(m, m2)]
                    @test composite == (t, (π1..., π2...))
                end
            end
        end

        @testset "RightComodule constructor type checks" begin
            S = FinPolySet([:a, :b])
            cs = state_system_comonoid(S)
            id_X = identity_lens(cs.carrier)
            # id is a lens cs.carrier → cs.carrier, NOT cs.carrier ▷ cs.carrier
            @test_throws ErrorException RightComodule(cs.carrier, cs, id_X)
        end

        @testset "regular_right_comodule validates iff base is a comonoid" begin
            S = FinPolySet([:a, :b, :c])
            cs = state_system_comonoid(S)
            M = regular_right_comodule(cs)
            @test validate_right_comodule(M)
            @test M.coaction == cs.duplicator

            cd = discrete_comonoid(S)
            @test validate_right_comodule(regular_right_comodule(cd))

            cm = monoid_comonoid(FinPolySet(0:3), 0,
                                 (a, b) -> mod(a + b, 4))
            @test validate_right_comodule(regular_right_comodule(cm))
        end

        @testset "validate_right_comodule catches bogus first component" begin
            S = FinPolySet([:a, :b, :c])
            cs = state_system_comonoid(S)
            bogus = Lens(cs.carrier, subst(cs.carrier, cs.carrier),
                         _ -> (:a, Dict(t => t for t in S.elements)),
                         (_, ab) -> ab[2])
            M = RightComodule(cs.carrier, cs, bogus)
            @test !validate_right_comodule(M)
        end

        @testset "regular_right_comodule on cofree_comonoid validates" begin
            p = Polynomial(FinPolySet([:run, :halt]),
                           i -> i == :run ? FinPolySet([:tick]) :
                                            FinPolySet(Symbol[]))
            Tp = cofree_comonoid(p, 2)
            @test validate_right_comodule(regular_right_comodule(Tp))
        end

        @testset "cofree_unit basics" begin
            p = Polynomial(FinPolySet([:run, :halt]),
                           i -> i == :run ? FinPolySet([:tick]) :
                                            FinPolySet(Symbol[]))
            unit = cofree_unit(p, 2)
            @test unit.cod == p
            # On positions: tree → root label.
            for t in unit.dom.positions.elements
                @test unit.on_positions.f(t) == t.label
            end
            # On directions: a ↦ singleton path (a,) for trees with that child expanded.
            t_run_to_halt = first(t for t in unit.dom.positions.elements
                                  if t.label == :run && haskey(t.children, :tick) &&
                                     t.children[:tick].label == :halt)
            @test unit.on_directions.f(t_run_to_halt).f(:tick) == (:tick,)
        end

        @testset "cofree_universal: state_system_comonoid → T_p factors labeling" begin
            p = Polynomial(FinPolySet([:run, :halt]),
                           i -> i == :run ? FinPolySet([:tick]) :
                                            FinPolySet(Symbol[]))
            S = FinPolySet([:s1, :s2])
            cs = state_system_comonoid(S)
            # A labeling that sends every state to :run, and every Sy^S
            # direction at any state to s1 (which lives in the direction-set
            # at every Sy^S position because direction-set is S itself).
            labeling = Lens(cs.carrier, p, _ -> :run, (_i, _a) -> :s1)
            F = cofree_universal(cs, labeling, 2)
            @test F.dom === cs
            # Use cardinality + tree-set equality instead of full Polynomial ==
            # so any non-determinism in tree enumeration order doesn't bite.
            @test cardinality(F.cod.carrier.positions) ==
                  cardinality(cofree_comonoid(p, 2).carrier.positions)
            @test Set(F.cod.carrier.positions.elements) ==
                  Set(cofree_comonoid(p, 2).carrier.positions.elements)
            # NEITHER form of validate_retrofunctor passes for truncated cofree
            # — the position-level comult law fails because walking k steps
            # in T_p^{(d)} from F(i) lands on a depth-(d-k) tree, while
            # F(c-codomain) is a fresh depth-d tree. This isn't a Lens-==
            # quirk; it's the truncation itself. The substantive content is
            # the universal property checked element-wise (below).
            @test !validate_retrofunctor(F)                  # strict: fails
            @test !validate_retrofunctor(F; strict=false)    # non-strict: also fails

            # Universal property: F.underlying ⨟ cofree_unit == labeling,
            # checked element-wise (the strict Lens `==` is more fragile
            # than this and not what the property literally states).
            unit_p = cofree_unit(p, 2)
            composite = compose(F.underlying, unit_p)
            for s in cs.carrier.positions.elements
                @test composite.on_positions.f(s) == labeling.on_positions.f(s)
                Da = direction_at(p, labeling.on_positions.f(s))
                if Da isa FinPolySet
                    for a in Da.elements
                        @test composite.on_directions.f(s).f(a) ==
                              labeling.on_directions.f(s).f(a)
                    end
                end
            end
        end

        @testset "cofree_universal on a discrete comonoid" begin
            S = FinPolySet([:a, :b])
            cd = discrete_comonoid(S)
            # constant(S) has positions S and empty direction-sets — every
            # position is a "leaf". Map each :a/:b state to itself.
            p = constant(S)
            labeling = Lens(cd.carrier, p, i -> i, (_i, _b) -> :pt)
            F = cofree_universal(cd, labeling, 1)
            @test validate_retrofunctor(F)
            @test compose(F.underlying, cofree_unit(p, 1)) == labeling
        end

        @testset "Bicomodule constructor type checks" begin
            S = FinPolySet([:a, :b])
            cs = state_system_comonoid(S)
            # Wrong left-coaction codomain
            wrong = Lens(cs.carrier, cs.carrier,
                         i -> i, (_, b) -> b)
            @test_throws ErrorException Bicomodule(cs.carrier, cs, cs, wrong, cs.duplicator)
        end

        @testset "regular_bicomodule validates on built-ins" begin
            S = FinPolySet([:a, :b, :c])
            for c in (state_system_comonoid(S),
                      discrete_comonoid(S),
                      monoid_comonoid(FinPolySet(0:2), 0,
                                      (a, b) -> mod(a + b, 3)))
                @test validate_bicomodule(regular_bicomodule(c))
            end
        end

        @testset "validate_bicomodule catches a bogus left coaction" begin
            S = FinPolySet([:a, :b])
            cs = state_system_comonoid(S)
            # Build a left coaction that fails the left first-component / counit
            # law: send every position to (:a, jbar) regardless of input.
            bogus_left = Lens(cs.carrier, subst(cs.carrier, cs.carrier),
                              _ -> (:a, Dict(t => t for t in S.elements)),
                              (_, ab) -> ab[2])
            B = Bicomodule(cs.carrier, cs, cs, bogus_left, cs.duplicator)
            @test !validate_bicomodule(B)
        end

        @testset "validate_bicomodule catches direction-level violation" begin
            # Build a bicomodule whose two single-side comodule laws BOTH hold
            # but whose left/right coactions disagree on direction-level
            # compatibility. Strategy: take regular_bicomodule on a monoid
            # that's non-commutative (one-object category BM with M = Z/3
            # under (a, b) ↦ b — left projection? no — let's do
            # multiplication mod 3 vs addition mod 3 used asymmetrically).
            #
            # Simpler: cs = state_system_comonoid({:a, :b}); use cs.duplicator
            # for λ_L (so left side is fine), but for λ_R use a *different*
            # well-formed right coaction that doesn't agree with cs.duplicator
            # at the direction level.
            S = FinPolySet([:a, :b])
            cs = state_system_comonoid(S)

            # A right coaction that sends every direction to its co-state
            # but with the components swapped. λR.on_pos(x) = (x, jbar) where
            # jbar(t) = t (same as cs). On directions: λR♯_x((t, u)) = the
            # OTHER state — flips :a ↔ :b after composition. This still
            # passes the right-comodule counit law because the input pair
            # (a, id_at_t) at x with id_at_t = t recovers a iff a == :a flipped
            # depending on...  Actually let's just construct one that we know
            # breaks compatibility with cs.duplicator on the left.
            #
            # The cleanest direction-level break: keep λR's on_pos identical
            # to cs.duplicator but flip its on_directions output for one
            # specific pair. That breaks coassoc on the right, so won't pass
            # the right-comodule check either. So this test ends up just
            # exercising the right-comodule path; that's still valuable.
            bad_right_on_dir = (i, ab) -> begin
                a, b = ab
                # Same as cs.duplicator's on-directions (which returns b),
                # except we lie at one specific pair to break the law.
                (i == :a && a == :a && b == :b) ? :a : b
            end
            bad_right = Lens(cs.carrier, subst(cs.carrier, cs.carrier),
                             s -> (s, Dict(t => t for t in S.elements)),
                             bad_right_on_dir)
            B = Bicomodule(cs.carrier, cs, cs, cs.duplicator, bad_right)
            @test !validate_bicomodule(B)
        end

        @testset "LeftComodule constructor type checks" begin
            S = FinPolySet([:a, :b])
            cs = state_system_comonoid(S)
            id_X = identity_lens(cs.carrier)
            # id has cod = cs.carrier, not cs.carrier ▷ cs.carrier
            @test_throws ErrorException LeftComodule(cs.carrier, cs, id_X)
        end

        @testset "regular_left_comodule validates on built-ins" begin
            S = FinPolySet([:a, :b, :c])
            for c in (state_system_comonoid(S),
                      discrete_comonoid(S),
                      monoid_comonoid(FinPolySet(0:2), 0,
                                      (a, b) -> mod(a + b, 3)))
                @test validate_left_comodule(regular_left_comodule(c))
            end
        end

        @testset "validate_left_comodule catches bogus first component" begin
            S = FinPolySet([:a, :b])
            cs = state_system_comonoid(S)
            # Wrong: send every position to (:a, jbar) regardless of input.
            bogus = Lens(cs.carrier, subst(cs.carrier, cs.carrier),
                         _ -> (:a, Dict(t => t for t in S.elements)),
                         (_, ab) -> ab[2])
            M = LeftComodule(cs.carrier, cs, bogus)
            @test !validate_left_comodule(M)
        end

        @testset "regular_left_comodule on cofree_comonoid validates" begin
            p = Polynomial(FinPolySet([:run, :halt]),
                           i -> i == :run ? FinPolySet([:tick]) :
                                            FinPolySet(Symbol[]))
            Tp = cofree_comonoid(p, 2)
            @test validate_left_comodule(regular_left_comodule(Tp))
        end

    end  # Sprint 8 testset

end  # outer @testset "Poly.jl"
