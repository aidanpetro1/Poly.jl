# ============================================================
# Extensions v1, PR #8: Symbolic ↔ concrete interop polish
# ============================================================
#
# Coverage:
#
#   1. to_symbolic / to_concrete aliases agree with lift / evaluate
#   2. Promotion in arithmetic: concrete + symbolic → symbolic
#   3. Promotion is symmetric (left and right operand)
#   4. All four operators promote: +, *, parallel, subst
#   5. Equality across worlds remains undefined (category-error)
#   6. to_concrete with bound environment

@testset "Extensions v1, PR #8: symbolic↔concrete interop" begin

    @testset "to_symbolic / to_concrete are aliases for lift / evaluate" begin
        p = @poly y^2 + y
        # Polynomial alias.
        @test to_symbolic(p) == lift(p)
        @test typeof(to_symbolic(p)) === SymbolicPolynomial

        # Lens alias.
        f = identity_lens(@poly y)
        @test to_symbolic(f) == lift(f)
        @test typeof(to_symbolic(f)) === SymbolicLens

        # to_concrete alias for evaluate.
        sp = to_symbolic(p)
        @test to_concrete(sp) == evaluate(sp)
        @test to_concrete(sp) == p
    end

    @testset "promotion: + with concrete and symbolic operands" begin
        p_concrete = @poly y^2
        sp = sympoly(:p)
        # concrete + symbolic
        result1 = p_concrete + sp
        @test result1 isa SymbolicPolynomial
        # symbolic + concrete (other side)
        result2 = sp + p_concrete
        @test result2 isa SymbolicPolynomial
    end

    @testset "promotion symmetric for *, parallel, subst" begin
        p_concrete = @poly y^2 + y
        sp = sympoly(:p)
        # *
        @test (p_concrete * sp) isa SymbolicPolynomial
        @test (sp * p_concrete) isa SymbolicPolynomial
        # parallel
        @test parallel(p_concrete, sp) isa SymbolicPolynomial
        @test parallel(sp, p_concrete) isa SymbolicPolynomial
        # subst (▷)
        @test subst(p_concrete, sp) isa SymbolicPolynomial
        @test subst(sp, p_concrete) isa SymbolicPolynomial
    end

    @testset "promotion preserves semantics: lift-then-op == op-then-lift" begin
        # Verify the auto-promote path is equivalent to manually lifting first,
        # by simplifying both sides and comparing.
        p_concrete = @poly y^2
        sp = sympoly(:p)
        auto = p_concrete + sp
        manual = lift(p_concrete) + sp
        @test sym_equal(auto, manual)
    end

    @testset "equality across worlds is intentionally undefined" begin
        # `==` between concrete Polynomial and SymbolicPolynomial isn't
        # promoted. Julia's default `==` falls back to `===` (identity) for
        # unrelated types — they're different objects, so this returns false.
        # Critically, it doesn't error or silently auto-evaluate.
        p_concrete = @poly y^2
        sp = to_symbolic(p_concrete)
        @test !(p_concrete == sp)        # not equal — different worlds
        @test !(sp == p_concrete)
        # The right way: evaluate the symbolic side and compare concretely.
        @test evaluate(sp) == p_concrete
        # Or use sym_equal after lifting both.
        @test sym_equal(to_symbolic(p_concrete), sp)
    end

    @testset "to_concrete with bound environment" begin
        p = sympoly(:p)
        expr = p + sym_y
        # Evaluate with :p bound to a concrete polynomial.
        result = to_concrete(expr, Dict(:p => @poly y^3))
        @test result isa Polynomial
        @test result == ((@poly y^3) + y)
    end

    @testset "to_concrete errors on unbound free variables" begin
        p = sympoly(:p)
        expr = p + sym_y
        @test_throws ErrorException to_concrete(expr)   # no env
    end

end  # @testset "Extensions v1, PR #8: symbolic↔concrete interop"
