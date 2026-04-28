# ============================================================
# @poly — terse polynomial construction
# ============================================================
#
# Lets you write polynomials the way the book does:
#
#   @poly y^3 + 2y + 1
#
# instead of the explicit-position form. Positions become anonymous integers
# (1, 2, ...) and direction-sets become anonymous integer ranges (1:k).
# Use the explicit `Polynomial(positions, dir_at)` form when you need
# meaningful labels.

"""
    @poly expr

Build a `Polynomial` from a polynomial-algebra expression.

# Examples
```julia
@poly y                    # the identity polynomial
@poly y^3                  # representable y^3
@poly 2y                   # linear with two positions
@poly 2y^3 + y + 1         # mixed
@poly 0                    # the zero polynomial
@poly 1                    # the constant polynomial 1
```

`y` is the only special name. Integer literals are interpreted as constant
polynomials (Niu & Spivak `n` ≅ `n y^0`).

Direction-sets are constructed as `FinPolySet(1:k)`, so all leaf labels are
anonymous integers. If you need to name positions or directions, use the
explicit `Polynomial(positions, dir_at_fn)` constructor instead.

# Equality caveat
Polynomials built by `@poly` use integer labels, while the canonical constants
`y`, `zero_poly`, `one_poly` use Symbol labels (`:pt`). Use `≈` (alias for
`is_iso`) when comparing across forms:
```julia
@poly y    ≈ y           # true (cardinality-iso)
@poly y    == y          # false (different label types)
```

# Operators recognized
The macro understands `+`, `*`, `^`, `▷`, and `⊗` as polynomial-algebra
operators, so you can write composite expressions inline:

```julia
@poly y^3 ▷ y^2          # = subst(y^3, y^2) ≈ y^6
@poly y^2 ⊗ y^3          # = parallel(y^2, y^3) ≈ y^6
@poly (y + 1) ▷ y^2      # left distributivity, etc.
```

Variables bound to a `Polynomial` in the surrounding scope are passed
through unchanged, so `@poly y^2 ▷ q` works when `q` is already a
Polynomial.

Anything the macro doesn't recognize falls through as a Julia expression,
so embedding macro output into a larger Julia expression works too:

```julia
(@poly y^3) ▷ q           # also fine — outer ▷ is just Julia
```
"""
macro poly(expr)
    return esc(_poly_expr(expr))
end

# Convert an Expr / Symbol / Int representing a polynomial-algebra expression
# into a Julia expression that builds the corresponding Polynomial.
function _poly_expr(e)
    # Bare `y`
    if e === :y
        return :($monomial($FinPolySet(1:1), $FinPolySet(1:1)))
    end

    # Integer literal: constant polynomial
    if e isa Integer
        return e == 0 ? :($zero_poly) :
               e == 1 ? :($one_poly)  :
                        :($constant($FinPolySet(1:$e)))
    end

    if e isa Expr && e.head === :call
        op = e.args[1]
        args = e.args[2:end]

        if op === :+
            # Variadic sum: foldl with `+` (the polynomial coproduct).
            terms = [_poly_expr(a) for a in args]
            return foldl((x, y) -> :($(x) + $(y)), terms)
        end

        if op === :^ && length(args) == 2 && args[1] === :y
            # y^k → representable y^k
            k = args[2]
            return :($monomial($FinPolySet(1:1), $FinPolySet(1:$k)))
        end

        if op === :*
            # Recognize n*y, n*y^k, y*y, ... at the polynomial level. The
            # only forms we accept here are scalar multiples of `y` or `y^k`,
            # which mean "n copies of that monomial". Anything else is
            # treated as polynomial cartesian product.
            if length(args) == 2
                lhs, rhs = args[1], args[2]
                # n * y or n * y^k
                if lhs isa Integer
                    if rhs === :y
                        return :($monomial($FinPolySet(1:$lhs), $FinPolySet(1:1)))
                    end
                    if rhs isa Expr && rhs.head === :call && length(rhs.args) == 3 &&
                       rhs.args[1] === :^ && rhs.args[2] === :y
                        k = rhs.args[3]
                        return :($monomial($FinPolySet(1:$lhs), $FinPolySet(1:$k)))
                    end
                end
                # y * n or y^k * n — symmetric form
                if rhs isa Integer
                    if lhs === :y
                        return :($monomial($FinPolySet(1:$rhs), $FinPolySet(1:1)))
                    end
                    if lhs isa Expr && lhs.head === :call && length(lhs.args) == 3 &&
                       lhs.args[1] === :^ && lhs.args[2] === :y
                        k = lhs.args[3]
                        return :($monomial($FinPolySet(1:$rhs), $FinPolySet(1:$k)))
                    end
                end
            end
            # Generic: treat as the polynomial-level cartesian product.
            terms = [_poly_expr(a) for a in args]
            return foldl((x, y) -> :($(x) * $(y)), terms)
        end

        if op === :- && length(args) == 1
            # Unary minus: not meaningful in **Poly** (no negatives). Reject.
            error("@poly: unary minus has no meaning for polynomial functors")
        end

        # ▷ — composition product (book's `◁`). Recurse on both sides so
        # `@poly y^2 ▷ q` works even when the right-hand side is a variable
        # already bound to a Polynomial. Same precedence as `*` in Julia,
        # so `@poly y + 2y ▷ q` is `(y) + ((2y) ▷ q)`.
        if op === :▷ && length(args) == 2
            return :($subst($(_poly_expr(args[1])), $(_poly_expr(args[2]))))
        end

        # ⊗ — parallel / Dirichlet product. Same treatment as ▷.
        if op === :⊗ && length(args) == 2
            return :($parallel($(_poly_expr(args[1])), $(_poly_expr(args[2]))))
        end
    end

    # Fallback: leave as-is. Allows `@poly y + foo` where `foo` is a
    # variable bound to a Polynomial in the surrounding scope.
    return e
end
