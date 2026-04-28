# ============================================================
# Symbolic layer (hybrid: lives alongside the concrete types)
# ============================================================
#
# This file provides expression-tree representations of polynomials and lenses
# so that we can build, manipulate, and verify equalities *symbolically* —
# without committing to a concrete enumeration. The concrete types
# (`Polynomial`, `Lens`, `PolyFunction`, ...) remain primary; the symbolic
# layer is parallel.
#
# The two layers connect via:
#   • `lift(::Polynomial)` and `lift(::Lens)` — concrete → symbolic
#   • `evaluate(::SymbolicPolynomial, env)` — symbolic → concrete, given an
#     environment binding free variables to concrete values.
#
# A small term-rewriting engine (`simplify`) reduces expressions using a list
# of rules. The rule set starts minimal and grows sprint by sprint.

# ----------------------------------------------------------------
# Expression types
# ----------------------------------------------------------------

"""
    SymExpr

Abstract supertype for symbolic expression trees in the polynomial-functor
theory. Two leaf forms (`SymVar`, `SymLit`) and one internal form (`SymOp`).
"""
abstract type SymExpr end

"""
    SymVar(name::Symbol, kind::Symbol)

A symbolic variable. `kind` records what *sort* of object the variable stands
for: `:Polynomial`, `:Lens`, `:Set`, `:Cardinality`. Useful for type-aware
rewriting (e.g., `id ⨟ f` rewrites only when `id` is a lens identity).
"""
struct SymVar <: SymExpr
    name::Symbol
    kind::Symbol
end

"""
    SymLit(value)

A symbolic literal: a wrapped concrete value (`Polynomial`, `Lens`,
`PolySet`, `Cardinality`, ...). Used so concrete inputs can sit inside an
otherwise-symbolic expression.
"""
struct SymLit <: SymExpr
    value::Any
end

"""
    SymOp(op::Symbol, args::Vector{SymExpr})

An operator application. The `op` symbol is one of:
  - polynomial-level: `:add` (+), `:mul` (×), `:par` (⊗), `:sub` (◁)
  - lens-level: `:compose`, `:id`, `:tensor` (⊗ on lenses), etc.
  - special: `:zero_poly`, `:one_poly`, `:y` (the polynomial constants)
"""
struct SymOp <: SymExpr
    op::Symbol
    args::Vector{SymExpr}
end

==(a::SymVar, b::SymVar) = a.name == b.name && a.kind == b.kind
==(a::SymLit, b::SymLit) = a.value == b.value
==(a::SymOp, b::SymOp) = a.op == b.op && a.args == b.args
==(::SymExpr, ::SymExpr) = false

hash(v::SymVar, h::UInt) = hash((:SymVar, v.name, v.kind), h)
hash(l::SymLit, h::UInt) = hash((:SymLit, l.value), h)
hash(o::SymOp, h::UInt) = hash((:SymOp, o.op, o.args), h)

function show(io::IO, v::SymVar)
    print(io, v.name)
end

function show(io::IO, l::SymLit)
    print(io, "⟦")
    show(io, l.value)
    print(io, "⟧")
end

function show(io::IO, o::SymOp)
    _show_prec(io, o, 0)
end

# Precedence-aware printing. `parent` is the precedence rank of the enclosing
# operator (0 = top-level). We add parens only when the current op has lower
# precedence than its parent, so `(p + q) ⊗ r` keeps parens but `p + q ⊗ r`
# prints without them.
function _show_prec(io::IO, e::SymVar, parent::Int)
    print(io, e.name)
end
function _show_prec(io::IO, e::SymLit, parent::Int)
    print(io, "⟦"); show(io, e.value); print(io, "⟧")
end
function _show_prec(io::IO, o::SymOp, parent::Int)
    sym = _op_glyph(o.op)
    if sym !== nothing && length(o.args) == 2
        my_prec = _show_prec_rank(o.op)
        need_parens = parent > my_prec
        need_parens && print(io, "(")
        _show_prec(io, o.args[1], my_prec)
        print(io, " ", sym, " ")
        # Right-associate: bump the precedence on the right so `a + b + c`
        # stays parens-free but `a + (b + c)` keeps inner parens when needed.
        _show_prec(io, o.args[2], my_prec + 1)
        need_parens && print(io, ")")
    elseif length(o.args) == 0
        print(io, _op_constant_name(o.op))
    elseif o.op === :id && length(o.args) == 1
        print(io, "id_")
        _show_prec(io, o.args[1], 100)
    else
        print(io, o.op, "(")
        for (k, a) in enumerate(o.args)
            k == 1 || print(io, ", ")
            _show_prec(io, a, 0)
        end
        print(io, ")")
    end
end

# Precedence ranks: higher binds tighter. Loose precedence shared with the
# LaTeX renderer below so the two stay in sync.
function _show_prec_rank(op::Symbol)
    op === :add     ? 10 :
    op === :compose ? 15 :
    op === :mul     ? 20 :
    op === :par     ? 20 :
    op === :sub     ? 25 :
    op === :tensor  ? 20 :
                       0
end

_op_glyph(op::Symbol) = op == :add      ? "+" :
                        op == :mul      ? "×" :
                        op == :par      ? "⊗" :
                        op == :sub      ? "◁" :
                        op == :compose  ? "⨟" :
                        op == :tensor   ? "⊗" :
                                          nothing

_op_constant_name(op::Symbol) = op == :zero_poly ? "0" :
                                 op == :one_poly ? "1" :
                                 op == :y        ? "y" :
                                                   string(op)

# ----------------------------------------------------------------
# Wrapper types: SymbolicPolynomial / SymbolicLens
# ----------------------------------------------------------------

"""
    SymbolicPolynomial(expr::SymExpr)

A polynomial described as an expression tree. Supports the four monoidal
operations (`+`, `*`, `⊗`, `◁`) and the constants `y`, `zero_poly`,
`one_poly`. Build symbolic polynomials with [`sympoly`](@ref) or by lifting
concrete polynomials with [`lift`](@ref).
"""
struct SymbolicPolynomial
    expr::SymExpr
end

"""
    SymbolicLens(expr::SymExpr; dom=nothing, cod=nothing)

A lens described as an expression tree. `dom` and `cod` are optional symbolic
polynomials carrying the type — useful for sanity-checking when building
expressions, but not required for pure rewriting.
"""
struct SymbolicLens
    expr::SymExpr
    dom::Union{SymbolicPolynomial,Nothing}
    cod::Union{SymbolicPolynomial,Nothing}
end
SymbolicLens(expr::SymExpr) = SymbolicLens(expr, nothing, nothing)

==(p::SymbolicPolynomial, q::SymbolicPolynomial) = p.expr == q.expr
==(f::SymbolicLens, g::SymbolicLens) = f.expr == g.expr
hash(p::SymbolicPolynomial, h::UInt) = hash((:SymPoly, p.expr), h)
hash(f::SymbolicLens, h::UInt) = hash((:SymLens, f.expr), h)

show(io::IO, p::SymbolicPolynomial) = show(io, p.expr)
show(io::IO, f::SymbolicLens) = (print(io, "SymLens("); show(io, f.expr); print(io, ")"))

# ----------------------------------------------------------------
# Polynomial constants & free variables
# ----------------------------------------------------------------

"""
    sym_y, sym_zero, sym_one

Symbolic polynomial constants — the symbolic analogues of `y`, `zero_poly`,
`one_poly`.
"""
const sym_y    = SymbolicPolynomial(SymOp(:y, SymExpr[]))
"""
    sym_zero :: SymbolicPolynomial

The symbolic zero polynomial — the lift of [`zero_poly`](@ref). Identity
for `+`, absorbing element for `*`, `parallel`, and `subst` in
the symbolic layer.
"""
const sym_zero = SymbolicPolynomial(SymOp(:zero_poly, SymExpr[]))
"""
    sym_one :: SymbolicPolynomial

The symbolic unit polynomial — the lift of [`one_poly`](@ref). Identity
for `*` (cartesian product) and absorbing element for `subst`
on the *left* (`one_poly ▷ p ≈ one_poly`).
"""
const sym_one  = SymbolicPolynomial(SymOp(:one_poly, SymExpr[]))

"""
    sympoly(name::Symbol) -> SymbolicPolynomial

A free symbolic polynomial variable.
"""
sympoly(name::Symbol) = SymbolicPolynomial(SymVar(name, :Polynomial))

"""
    symlens(name::Symbol; dom=nothing, cod=nothing) -> SymbolicLens

A free symbolic lens variable.
"""
symlens(name::Symbol; dom=nothing, cod=nothing) =
    SymbolicLens(SymVar(name, :Lens), dom, cod)

# ----------------------------------------------------------------
# Operations on SymbolicPolynomial
# ----------------------------------------------------------------
#
# Commutative operators (`+`, `*`, `par`) sort their arguments by a
# stable key at construction time so that `p + q` and `q + p` produce
# `==` expressions. The non-commutative `sub` (◁) does not sort.

_expr_key(e::SymExpr) = sprint(show, e)

function _sort_args(a::SymExpr, b::SymExpr)
    _expr_key(a) ≤ _expr_key(b) ? (a, b) : (b, a)
end

function +(p::SymbolicPolynomial, q::SymbolicPolynomial)
    a, b = _sort_args(p.expr, q.expr)
    SymbolicPolynomial(SymOp(:add, SymExpr[a, b]))
end

function *(p::SymbolicPolynomial, q::SymbolicPolynomial)
    a, b = _sort_args(p.expr, q.expr)
    SymbolicPolynomial(SymOp(:mul, SymExpr[a, b]))
end

"""
    parallel(p::SymbolicPolynomial, q::SymbolicPolynomial) -> SymbolicPolynomial

The Dirichlet / parallel product `p ⊗ q`, symbolic.
"""
function parallel(p::SymbolicPolynomial, q::SymbolicPolynomial)
    a, b = _sort_args(p.expr, q.expr)
    SymbolicPolynomial(SymOp(:par, SymExpr[a, b]))
end

"""
    subst(p::SymbolicPolynomial, q::SymbolicPolynomial) -> SymbolicPolynomial

The composition product `p ◁ q` (substitution / time evolution), symbolic.
Asymmetric — does *not* sort args.
"""
subst(p::SymbolicPolynomial, q::SymbolicPolynomial) =
    SymbolicPolynomial(SymOp(:sub, SymExpr[p.expr, q.expr]))

# ----------------------------------------------------------------
# Operations on SymbolicLens
# ----------------------------------------------------------------

"""
    compose(f::SymbolicLens, g::SymbolicLens) -> SymbolicLens

Vertical composition `f ⨟ g`, symbolic.
"""
compose(f::SymbolicLens, g::SymbolicLens) =
    SymbolicLens(SymOp(:compose, SymExpr[f.expr, g.expr]),
                 f.dom, g.cod)

"""
    sym_id(p::SymbolicPolynomial) -> SymbolicLens

The symbolic identity lens `id_p : p → p`.
"""
sym_id(p::SymbolicPolynomial) =
    SymbolicLens(SymOp(:id, SymExpr[p.expr]), p, p)

# ----------------------------------------------------------------
# Lift: concrete → symbolic
# ----------------------------------------------------------------

"""
    lift(p::Polynomial; name::Symbol=:p) -> SymbolicPolynomial

Lift a concrete polynomial to the symbolic layer. By default, wraps the
concrete value as a `SymLit`. Pass `name` to introduce a free variable
instead — useful for stating polynomial-shaped theorems abstractly.

Lifting recognizes the special-class constants (`y`, `zero_poly`, `one_poly`)
and produces the corresponding symbolic constants directly.
"""
function lift(p::Polynomial; name::Union{Symbol,Nothing}=nothing)
    if name !== nothing
        return SymbolicPolynomial(SymVar(name, :Polynomial))
    end
    p === y         && return sym_y
    p === zero_poly && return sym_zero
    p === one_poly  && return sym_one
    p == y          && return sym_y
    p == zero_poly  && return sym_zero
    p == one_poly   && return sym_one
    SymbolicPolynomial(SymLit(p))
end

"""
    lift(f::Lens; name::Symbol=:f) -> SymbolicLens

Lift a concrete lens to the symbolic layer.
"""
function lift(f::Lens; name::Union{Symbol,Nothing}=nothing)
    if name !== nothing
        return SymbolicLens(SymVar(name, :Lens), lift(f.dom), lift(f.cod))
    end
    SymbolicLens(SymLit(f), lift(f.dom), lift(f.cod))
end

# ----------------------------------------------------------------
# Evaluate: symbolic → concrete (when leaves are concretizable)
# ----------------------------------------------------------------

"""
    evaluate(p::SymbolicPolynomial, env::Dict{Symbol,Polynomial}=Dict()) -> Polynomial

Reduce a symbolic polynomial to a concrete `Polynomial`. Free variables are
looked up in `env`. Operators are evaluated using the concrete-layer
implementations (which Sprint 3 will provide for `+`, `×`, `⊗`, `◁`).

For Sprint 1+2 we only support the no-op cases: literals, variable lookup,
and the constants `y`, `zero_poly`, `one_poly`. Sprint 3 will dispatch the
binary ops to their concrete counterparts.
"""
function evaluate(p::SymbolicPolynomial, env::Dict{Symbol,Polynomial}=Dict{Symbol,Polynomial}())
    _eval(p.expr, env)
end

function _eval(e::SymVar, env)
    haskey(env, e.name) || error("Unbound symbolic variable :$(e.name) of kind :$(e.kind)")
    env[e.name]
end
_eval(e::SymLit, _) = e.value
function _eval(e::SymOp, env)
    e.op == :y         && return y
    e.op == :zero_poly && return zero_poly
    e.op == :one_poly  && return one_poly
    # Sprint 3: concrete monoidal products
    if e.op == :add && length(e.args) == 2
        return _eval(e.args[1], env) + _eval(e.args[2], env)
    elseif e.op == :mul && length(e.args) == 2
        return _eval(e.args[1], env) * _eval(e.args[2], env)
    elseif e.op == :par && length(e.args) == 2
        return parallel(_eval(e.args[1], env), _eval(e.args[2], env))
    end
    # Sprint 4: composition product
    if e.op == :sub && length(e.args) == 2
        return subst(_eval(e.args[1], env), _eval(e.args[2], env))
    end
    # Lens-level ops come in later sprints.
    error("evaluate: operator :$(e.op) has no concrete implementation yet.")
end

# ----------------------------------------------------------------
# Term rewriting: simplify
# ----------------------------------------------------------------

"""
    Rule(lhs::SymExpr, rhs::SymExpr; description::String="")

A single rewrite rule. Matches `lhs` (with `SymVar`s acting as pattern
variables) and replaces with `rhs` after substitution.
"""
struct Rule
    lhs::SymExpr
    rhs::SymExpr
    description::String
end
Rule(lhs::SymExpr, rhs::SymExpr) = Rule(lhs, rhs, "")

"""
    rules() -> Vector{Rule}

The current rewrite-rule registry. Sprint-by-sprint, more rules join.

Sprint 1+2:
  - lens identity laws: `f ⨟ id = f`, `id ⨟ f = f`
  - polynomial unitors for `+`, `×`, `⊗`, `◁`

Sprint 3:
  - zero/one absorption for `×` and `⊗`: `p × 0 = 0`, `0 × p = 0`,
    `p ⊗ 0 = 0`, `0 ⊗ p = 0`
  - associativity (right-associate): `(a + b) + c → a + (b + c)`, similarly
    for `×` and `⊗`
  - distributivity (expand): `(a + b) × c → (a × c) + (b × c)` and the
    symmetric forms; same for `⊗`

Commutativity is not encoded as rewrite rules — instead, the `+`, `*`, and
`parallel` operators on `SymbolicPolynomial` sort their arguments at
construction time so commuted-pair expressions are structurally equal.
"""
function rules()
    f = SymVar(:f, :Lens)
    p = SymVar(:p, :Polynomial)
    a = SymVar(:a, :Polynomial)
    b = SymVar(:b, :Polynomial)
    c = SymVar(:c, :Polynomial)
    zero_e = SymOp(:zero_poly, SymExpr[])
    one_e  = SymOp(:one_poly,  SymExpr[])
    y_e    = SymOp(:y,         SymExpr[])

    [
        # ------- Lens identity laws (vertical composition) --------
        Rule(SymOp(:compose, SymExpr[f, SymOp(:id, SymExpr[SymVar(:_anything, :Polynomial)])]),
             f, "f ⨟ id = f"),
        Rule(SymOp(:compose, SymExpr[SymOp(:id, SymExpr[SymVar(:_anything, :Polynomial)]), f]),
             f, "id ⨟ f = f"),

        # ------- Polynomial unitors --------
        Rule(SymOp(:add, SymExpr[p, zero_e]), p, "p + 0 = p"),
        Rule(SymOp(:add, SymExpr[zero_e, p]), p, "0 + p = p"),
        Rule(SymOp(:mul, SymExpr[p, one_e]),  p, "p × 1 = p"),
        Rule(SymOp(:mul, SymExpr[one_e, p]),  p, "1 × p = p"),
        Rule(SymOp(:par, SymExpr[p, y_e]),    p, "p ⊗ y = p"),
        Rule(SymOp(:par, SymExpr[y_e, p]),    p, "y ⊗ p = p"),
        Rule(SymOp(:sub, SymExpr[p, y_e]),    p, "p ◁ y = p"),
        Rule(SymOp(:sub, SymExpr[y_e, p]),    p, "y ◁ p = p"),

        # ------- Zero absorption for × and ⊗ --------
        Rule(SymOp(:mul, SymExpr[p, zero_e]), zero_e, "p × 0 = 0"),
        Rule(SymOp(:mul, SymExpr[zero_e, p]), zero_e, "0 × p = 0"),
        Rule(SymOp(:par, SymExpr[p, zero_e]), zero_e, "p ⊗ 0 = 0"),
        Rule(SymOp(:par, SymExpr[zero_e, p]), zero_e, "0 ⊗ p = 0"),

        # ------- Associativity (right-associate) --------
        Rule(SymOp(:add, SymExpr[SymOp(:add, SymExpr[a, b]), c]),
             SymOp(:add, SymExpr[a, SymOp(:add, SymExpr[b, c])]),
             "(a + b) + c = a + (b + c)"),
        Rule(SymOp(:mul, SymExpr[SymOp(:mul, SymExpr[a, b]), c]),
             SymOp(:mul, SymExpr[a, SymOp(:mul, SymExpr[b, c])]),
             "(a × b) × c = a × (b × c)"),
        Rule(SymOp(:par, SymExpr[SymOp(:par, SymExpr[a, b]), c]),
             SymOp(:par, SymExpr[a, SymOp(:par, SymExpr[b, c])]),
             "(a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)"),

        # ------- Distributivity (expand: × over +, ⊗ over +) --------
        Rule(SymOp(:mul, SymExpr[SymOp(:add, SymExpr[a, b]), c]),
             SymOp(:add, SymExpr[SymOp(:mul, SymExpr[a, c]),
                                 SymOp(:mul, SymExpr[b, c])]),
             "(a + b) × c = (a × c) + (b × c)"),
        Rule(SymOp(:mul, SymExpr[c, SymOp(:add, SymExpr[a, b])]),
             SymOp(:add, SymExpr[SymOp(:mul, SymExpr[c, a]),
                                 SymOp(:mul, SymExpr[c, b])]),
             "c × (a + b) = (c × a) + (c × b)"),
        Rule(SymOp(:par, SymExpr[SymOp(:add, SymExpr[a, b]), c]),
             SymOp(:add, SymExpr[SymOp(:par, SymExpr[a, c]),
                                 SymOp(:par, SymExpr[b, c])]),
             "(a + b) ⊗ c = (a ⊗ c) + (b ⊗ c)"),
        Rule(SymOp(:par, SymExpr[c, SymOp(:add, SymExpr[a, b])]),
             SymOp(:add, SymExpr[SymOp(:par, SymExpr[c, a]),
                                 SymOp(:par, SymExpr[c, b])]),
             "c ⊗ (a + b) = (c ⊗ a) + (c ⊗ b)"),

        # ------- Composition product ◁ (Sprint 4) --------
        # Left distributivity (Niu & Spivak §6.3.1, Proposition 6.47):
        # NOT right-distributive — `r ◁ (p + q) ≠ (r ◁ p) + (r ◁ q)` in general.
        Rule(SymOp(:sub, SymExpr[SymOp(:add, SymExpr[a, b]), c]),
             SymOp(:add, SymExpr[SymOp(:sub, SymExpr[a, c]),
                                 SymOp(:sub, SymExpr[b, c])]),
             "(a + b) ◁ c = (a ◁ c) + (b ◁ c)"),
        Rule(SymOp(:sub, SymExpr[SymOp(:mul, SymExpr[a, b]), c]),
             SymOp(:mul, SymExpr[SymOp(:sub, SymExpr[a, c]),
                                 SymOp(:sub, SymExpr[b, c])]),
             "(a × b) ◁ c = (a ◁ c) × (b ◁ c)"),

        # Constants under ◁ on the left
        Rule(SymOp(:sub, SymExpr[zero_e, p]), zero_e, "0 ◁ p = 0"),
        Rule(SymOp(:sub, SymExpr[one_e,  p]), one_e,  "1 ◁ p = 1"),
    ]
end

# Pattern matching: a SymVar in the LHS acts as a wildcard. We collect a
# substitution mapping (var name) → SymExpr; if a variable appears more than
# once in the LHS, all its occurrences must match the same expression.
const _Subst = Dict{Symbol,SymExpr}

function _match(pattern::SymExpr, expr::SymExpr, subst::_Subst=_Subst())
    if pattern isa SymVar
        # Wildcard: any expression matches. Names starting with `_` are anonymous.
        haskey(subst, pattern.name) && pattern.name !== :_anything &&
            return subst[pattern.name] == expr ? subst : nothing
        if pattern.name !== :_anything
            new_subst = copy(subst)
            new_subst[pattern.name] = expr
            return new_subst
        end
        return subst
    elseif pattern isa SymLit
        return (expr isa SymLit && pattern.value == expr.value) ? subst : nothing
    elseif pattern isa SymOp
        expr isa SymOp || return nothing
        pattern.op == expr.op || return nothing
        length(pattern.args) == length(expr.args) || return nothing
        s = subst
        for (pa, ea) in zip(pattern.args, expr.args)
            s = _match(pa, ea, s)
            s === nothing && return nothing
        end
        return s
    end
    nothing
end

function _substitute(expr::SymExpr, subst::_Subst)
    if expr isa SymVar
        return get(subst, expr.name, expr)
    elseif expr isa SymLit
        return expr
    elseif expr isa SymOp
        return SymOp(expr.op, SymExpr[_substitute(a, subst) for a in expr.args])
    end
    expr
end

# Bottom-up rewrite. Returns `(new_expr, applied_rule_or_nothing)`. The first
# rule application along the recursive walk is reported; if multiple rules
# could fire, only one is applied per call.
function _try_rewrite(expr::SymExpr, rs::Vector{Rule})
    if expr isa SymOp
        new_args = SymExpr[]
        applied = nothing
        for a in expr.args
            a2, r = _try_rewrite(a, rs)
            push!(new_args, a2)
            if r !== nothing && applied === nothing
                applied = r
            end
        end
        if applied !== nothing
            return (SymOp(expr.op, new_args), applied)
        end
        # Children unchanged: try root-level rules.
        for r in rs
            s = _match(r.lhs, expr)
            s === nothing && continue
            return (_substitute(r.rhs, s), r)
        end
        return (expr, nothing)
    end
    for r in rs
        s = _match(r.lhs, expr)
        s === nothing && continue
        return (_substitute(r.rhs, s), r)
    end
    return (expr, nothing)
end

"""
    simplify(p::SymbolicPolynomial; max_iters=64, trace=false)
    simplify(f::SymbolicLens; max_iters=64, trace=false)

Apply [`rules`](@ref) repeatedly until a fixed point or `max_iters` rounds
elapse.

When `trace=true`, returns a tuple `(simplified, history)` where `history` is
a `Vector{Tuple{Rule, SymExpr}}` listing each rule that fired and the
intermediate expression after firing it. Useful for debugging unexpected
non-reductions.
"""
function simplify(p::SymbolicPolynomial; max_iters::Int=64, trace::Bool=false)
    rs = rules()
    e = p.expr
    history = Tuple{Rule,SymExpr}[]
    for _ in 1:max_iters
        e2, applied = _try_rewrite(e, rs)
        if applied === nothing || e2 == e
            return trace ? (SymbolicPolynomial(e2), history) : SymbolicPolynomial(e2)
        end
        if trace
            push!(history, (applied, e2))
        end
        e = e2
    end
    trace ? (SymbolicPolynomial(e), history) : SymbolicPolynomial(e)
end

function simplify(f::SymbolicLens; max_iters::Int=64, trace::Bool=false)
    rs = rules()
    e = f.expr
    history = Tuple{Rule,SymExpr}[]
    for _ in 1:max_iters
        e2, applied = _try_rewrite(e, rs)
        if applied === nothing || e2 == e
            return trace ? (SymbolicLens(e2, f.dom, f.cod), history) :
                            SymbolicLens(e2, f.dom, f.cod)
        end
        if trace
            push!(history, (applied, e2))
        end
        e = e2
    end
    trace ? (SymbolicLens(e, f.dom, f.cod), history) :
            SymbolicLens(e, f.dom, f.cod)
end

"""
    sym_equal(a::SymbolicPolynomial, b::SymbolicPolynomial) -> Bool
    sym_equal(a::SymbolicLens, b::SymbolicLens) -> Bool

Decide equality by simplifying both sides and comparing structurally. This is
*not* complete (there are many equalities the rule set can't yet derive), but
it's sound: if `sym_equal(a, b)` returns `true`, then `a == b` holds in
**Poly**.
"""
sym_equal(a::SymbolicPolynomial, b::SymbolicPolynomial) =
    simplify(a) == simplify(b)
sym_equal(a::SymbolicLens, b::SymbolicLens) =
    simplify(a) == simplify(b)

"""
    p ≈ q  for SymbolicPolynomial / SymbolicLens

Unicode alias for [`sym_equal`](@ref). Decides equality by simplifying both
sides via [`simplify`](@ref) and comparing the resulting expression trees.
Sound but incomplete — `a ≈ b` ⇒ `a == b` in **Poly**, but the converse may
fail when `simplify`'s rule set isn't strong enough to reduce both sides.
"""
Base.:≈(a::SymbolicPolynomial, b::SymbolicPolynomial) = sym_equal(a, b)
Base.:≈(a::SymbolicLens, b::SymbolicLens) = sym_equal(a, b)

# ----------------------------------------------------------------
# LaTeX rendering
# ----------------------------------------------------------------

"""
    to_latex(x) -> String

Render `x` as a LaTeX math-mode string (no surrounding `\$ ... \$`). Defined
for `SymExpr`, `SymbolicPolynomial`, `SymbolicLens`, `Polynomial`, `Lens`,
and the leaf cardinality types.

Operator glyphs:
  - polynomial sum  → `+`
  - polynomial prod → `\\cdot`
  - parallel ⊗      → `\\otimes`
  - composition ◁   → `\\triangleleft`
  - lens compose ⨟  → `\\fatsemi`  (load `stmaryrd` in your TeX preamble)
  - identity lens   → `\\mathrm{id}_{p}`

Use [`latex_display`](@ref) to wrap in `\$\$ ... \$\$` for inline preview.
"""
to_latex(p::SymbolicPolynomial) = _latex_expr(p.expr; precedence=0)
to_latex(f::SymbolicLens)       = _latex_expr(f.expr; precedence=0)

# Operator precedence (higher binds tighter): used to decide when to add parens.
const _PREC = Dict(
    :add     => 10,  # +
    :mul     => 20,  # ·
    :par     => 20,  # ⊗
    :sub     => 25,  # ◁
    :compose => 15,  # ⨟
    :tensor  => 20,  # ⊗ (lens-level)
)

function _latex_expr(e::SymVar; precedence::Int=0)
    string(e.name)
end

function _latex_expr(e::SymLit; precedence::Int=0)
    v = e.value
    if v isa Polynomial
        return to_latex(v)
    elseif v isa Lens
        return to_latex(v)
    elseif v isa Cardinality
        return to_latex(v)
    end
    # Generic literal: just escape and wrap.
    "\\mathit{" * string(v) * "}"
end

function _latex_expr(e::SymOp; precedence::Int=0)
    op = e.op
    args = e.args

    # Constants
    op === :y         && return "y"
    op === :zero_poly && return "0"
    op === :one_poly  && return "1"

    # Identity lens: id_{...}
    if op === :id && length(args) == 1
        return "\\mathrm{id}_{" * _latex_expr(args[1]; precedence=0) * "}"
    end

    # Binary infix operators
    if length(args) == 2 && haskey(_PREC, op)
        my_prec = _PREC[op]
        glyph = op === :add     ? "+"            :
                op === :mul     ? "\\cdot"       :
                op === :par     ? "\\otimes"     :
                op === :sub     ? "\\triangleleft" :
                op === :compose ? "\\fatsemi"    :
                op === :tensor  ? "\\otimes"     : "?"
        left  = _latex_expr(args[1]; precedence=my_prec)
        right = _latex_expr(args[2]; precedence=my_prec + 1)  # right-assoc would be `my_prec`
        s = left * " " * glyph * " " * right
        return precedence > my_prec ? "\\left(" * s * "\\right)" : s
    end

    # Unknown / generic: render as op(args...)
    inner = join((_latex_expr(a; precedence=0) for a in args), ", ")
    "\\mathrm{" * string(op) * "}\\left(" * inner * "\\right)"
end

# ---- LaTeX for concrete types ----

"""
    to_latex(p::Polynomial) -> String

LaTeX rendering of a concrete polynomial in book-canonical form (summands
merged by direction-set cardinality), e.g. `y^{3} + 2y^{2} + 1`.
"""
function to_latex(p::Polynomial)
    s = _summarize_polynomial_merged(p)
    s === nothing && return "\\mathit{Polynomial}"
    isempty(s) && return "0"
    parts = String[]
    for (n, cd) in s
        coef = n == 1 ? "" : string(n)
        if cd == Finite(0)
            push!(parts, n == 1 ? "1" : string(n))
        elseif cd == Finite(1)
            push!(parts, coef * "y")
        elseif cd isa Finite
            push!(parts, coef * "y^{" * string(cd.n) * "}")
        else
            push!(parts, coef * "y^{" * to_latex(cd) * "}")
        end
    end
    join(parts, " + ")
end

"""
    to_latex(f::Lens) -> String

LaTeX rendering of a concrete lens as `p \\to q` (just the type signature;
on-positions/on-directions content isn't standard LaTeX-able without a
diagram). For richer output, use `PolyViz.render_polybox`.
"""
to_latex(f::Lens) = to_latex(f.dom) * " \\to " * to_latex(f.cod)

# ---- LaTeX for cardinality leaves ----

to_latex(c::Finite)              = string(c.n)
to_latex(::CountablyInfinite)    = "\\aleph_{0}"
to_latex(::Continuum)            = "\\mathfrak{c}"
to_latex(c::SymbolicCardinality) = "\\lvert " * string(c.name) * " \\rvert"
function to_latex(e::CardinalityExpr)
    glyph = e.op === :+ ? "+" : e.op === :* ? "\\cdot" : "^"
    a = to_latex(e.args[1])
    b = to_latex(e.args[2])
    if e.op === :^
        return a * "^{" * b * "}"
    end
    "\\left(" * a * " " * glyph * " " * b * "\\right)"
end

"""
    latex_display(x) -> String

Wrap [`to_latex`](@ref) in `\$\$ ... \$\$` delimiters so the result can be
pasted into Markdown / Jupyter / a TeX document directly.
"""
latex_display(x) = "\$\$ " * to_latex(x) * " \$\$"
