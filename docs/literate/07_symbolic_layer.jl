# # The symbolic layer
#
# Alongside the concrete types (`Polynomial`, `Lens`, ...), `Poly.jl` ships a
# parallel *symbolic* layer for working up to isomorphism, verifying book
# identities, and reasoning about polynomials whose sets are infinite or
# named-only.

using Poly

# ## Symbolic polynomials
#
# `sympoly(:p)` makes a polynomial-valued variable. The constants `sym_y`,
# `sym_zero`, `sym_one` are the symbolic versions of `y`, `zero_poly`,
# `one_poly`.

p = sympoly(:p)
q = sympoly(:q)
r = sympoly(:r)

# All four monoidal operations work on symbolic polynomials via Julia
# dispatch — same syntax as the concrete versions.

p + q,  p * q,  parallel(p, q),  p ▷ q

# Mixed concrete + symbolic operands fall through to symbolic. `lift`
# embeds a concrete polynomial into the symbolic AST.

lift(@poly y^2 + 1)

# ## Term rewriting: `simplify`
#
# `simplify(expr)` repeatedly applies the rewrite rules in `rules()` until
# a fixed point. With `trace=true`, it also returns a step-by-step history.

simplify(p + sym_zero)             # unitor: p + 0 = p
#-
simplify(parallel(sym_zero, p))    # absorbing: 0 ⊗ p = 0
#-
simplify(parallel(p + q, r))       # distributivity: (p + q) ⊗ r = (p ⊗ r) + (q ⊗ r)

# A trace tells you *which* rules fired and in what order.

result, history = simplify(parallel(p + q, r); trace=true)
[(rule.description, intermediate) for (rule, intermediate) in history]

# ## Equality up to rewriting: `sym_equal`
#
# `sym_equal(a, b)` simplifies both sides and compares the normal forms.
# This is the right notion of equality for verifying book identities.

sym_equal(parallel(p + q, r), parallel(p, r) + parallel(q, r))    # Niu/Spivak Ex. 3.77
#-
sym_equal((p + q) ▷ r, (p ▷ r) + (q ▷ r))                         # Niu/Spivak Prop 6.47

# Note `▷` is left-distributive but **not** right-distributive — the
# rewrite rule set respects this:

sym_equal(p ▷ (q + r), (p ▷ q) + (p ▷ r))                        # false

# ## The rule registry
#
# `rules()` returns the active list of `Rule` values. Each rule is an LHS /
# RHS pair plus a human-readable description.

length(rules()), first(rules()).description

# Rules currently encoded (sample):

[r.description for r in rules()[1:8]]

# ## Lifting and evaluation
#
# `lift(x)` raises a concrete object into the symbolic AST. `evaluate(expr,
# env)` does the inverse: walks the symbolic tree, looking up free
# variables in `env::Dict`, and returns a concrete result.

env = Dict(:p => (@poly y^2), :q => (@poly y + 1))
evaluate(sympoly(:p) + sympoly(:q), env)
#-
evaluate(parallel(sympoly(:p), sympoly(:q)), env)

# This bridges the two layers: do your reasoning symbolically, instantiate
# concretely when you need to compute.

# ## Symbolic lenses
#
# `symlens(:f, dom=p, cod=q)` builds a free lens variable. Useful for
# verifying lens-equational identities. `sym_id(p)` is the symbolic
# identity at `p`.

f = symlens(:f, dom=p, cod=q)
id_p = sym_id(p)
simplify(compose(f, id_p))         # right-identity: f ⨟ id_p = f
#-
simplify(compose(sym_id(p), f))    # left-identity:  id_p ⨟ f = f

# ## LaTeX rendering
#
# `to_latex(expr)` renders a symbolic polynomial as a LaTeX string;
# `latex_display(expr)` wraps it in `$$...$$` for use in Jupyter / Pluto.

to_latex(parallel(p + q, r))
#-
latex_display(p ▷ q + sym_y)
