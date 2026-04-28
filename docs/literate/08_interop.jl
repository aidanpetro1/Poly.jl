# # Concrete ↔ symbolic interop
#
# `Poly.jl` keeps two parallel layers: the **concrete** types
# (`Polynomial`, `Lens`, `PolyFunction`, ...) that materialize their
# data, and the **symbolic** types (`SymbolicPolynomial`, `SymbolicLens`)
# that build expression trees. Concrete is where computation happens;
# symbolic is where reasoning happens. This tour walks the boundary
# between them: when to lift, when to evaluate, what auto-promotes,
# and what stays explicit on purpose.

using Poly

# ## Lifting concrete polynomials
#
# `to_symbolic` (alias `lift`) embeds a concrete polynomial into the
# symbolic AST. Special-case constants (`y`, `zero_poly`, `one_poly`)
# are recognized and produce the matching symbolic constants.

p_concrete = @poly y^2 + y     # a concrete polynomial, two positions
p_sym      = to_symbolic(p_concrete)
typeof(p_sym)

# Lifted concrete polynomials live as `SymLit` leaves in the AST. Free
# variables are introduced via `sympoly`:

p = sympoly(:p)
q = sympoly(:q)
typeof(p), typeof(q)

# ## Auto-promotion in arithmetic
#
# When you mix a concrete and a symbolic operand in `+`, `*`, `parallel`,
# or `subst`, the concrete operand is silently lifted and the result is
# symbolic. The four arithmetic operators all promote:

p_concrete + p             # concrete + symbolic → symbolic
p * p_concrete             # symbolic * concrete → symbolic
parallel(p_concrete, q)    # parallel — same rule
subst(p, p_concrete)       # ◁ — same rule

# This lets you write the natural shape — `p + my_concrete_polynomial`
# — without `lift(my_concrete_polynomial) + p` boilerplate at every
# call site.

# ## What does *not* auto-promote: equality
#
# `==` between a concrete and a symbolic polynomial is **intentionally
# undefined**. Comparing across the boundary is a category error: a
# concrete polynomial and a `SymbolicPolynomial` whose `evaluate` would
# produce the same concrete polynomial are not the *same kind of
# object*. If you want to compare semantically, either:

# * `evaluate` the symbolic side and compare concretely:

evaluate(p_sym) == p_concrete

# * or `to_symbolic` the concrete side and use `sym_equal` for
#   up-to-rewriting equality:

sym_equal(p_sym, to_symbolic(p_concrete))

# Both paths force you to declare which world you mean. Auto-promoting
# `==` would silently paper over genuine type mismatches.

# ## Going back: `to_concrete`
#
# `to_concrete` (alias `evaluate`) reduces a symbolic expression to a
# concrete `Polynomial`. Free variables get looked up in an
# environment dict:

p_with_var = p + sym_y            # symbolic: p + y
to_concrete(p_with_var, Dict(:p => @poly y^3))

# If you call `to_concrete` on an expression with unbound variables,
# you get an error. The boundary is sharp on purpose.

# ## Style guide for the boundary
#
# Prefer `to_symbolic` / `to_concrete` at *boundary-crossing* call sites
# where direction is what's important:

f_concrete = identity_lens(@poly y)
to_symbolic(f_concrete)            # boundary cross: direction matters

# Prefer `lift` / `evaluate` inside symbolic-layer code where the names
# read like normal operations:

simplify(lift(@poly y^2) + sym_y)  # natural inside symbolic-layer prose

# Both are aliases — same function, same semantics — so pick the one
# that reads better in context.

# ## Things to remember
#
# * Mixed-type arithmetic returns symbolic.
# * Equality across types is undefined — choose your world first.
# * `to_concrete` errors on unbound variables; bind them with `env`.
# * Aliases: `to_symbolic = lift`, `to_concrete = evaluate`.
