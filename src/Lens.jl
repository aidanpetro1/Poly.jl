# ============================================================
# Lens (Sprint 2)
# ============================================================

"""
    Lens(dom::Polynomial, cod::Polynomial,
         on_positions::PolyFunction, on_directions::DependentFunction)

A dependent lens `f : dom → cod` between two polynomials, characterized
(per Niu & Spivak Proposition 3.6) by a pair `(f₁, f♯)`:

- `on_positions :: PolyFunction` — the forward `f₁ : dom(1) → cod(1)`.
- `on_directions :: DependentFunction` — for each `i ∈ dom(1)`, a `PolyFunction`
  `f♯_i : cod[f₁ i] → dom[i]` (note the *reversed* direction).

Lenses are the morphisms of the category **Poly**.

Access fields directly: `f.on_positions`, `f.on_directions`.
"""
struct Lens
    dom::Polynomial
    cod::Polynomial
    on_positions::PolyFunction
    on_directions::DependentFunction
    function Lens(dom, cod, on_pos::PolyFunction, on_dir::DependentFunction)
        on_pos.dom == dom.positions || error("on_positions domain $(on_pos.dom) ≠ dom.positions $(dom.positions)")
        on_pos.cod == cod.positions || error("on_positions codomain $(on_pos.cod) ≠ cod.positions $(cod.positions)")
        on_dir.dom == dom.positions || error("on_directions domain $(on_dir.dom) ≠ dom.positions $(dom.positions)")
        new(dom, cod, on_pos, on_dir)
    end
end

"""
    Lens(dom, cod, on_pos_fn::Function, on_dir_fn::Function)

Convenience constructor.
- `on_pos_fn(i)` returns a `cod`-position for each `i ∈ dom(1)`.
- `on_dir_fn(i, b)` returns a `dom[i]`-direction for each `i ∈ dom(1)` and
  `b ∈ cod[on_pos_fn(i)]`.
"""
function Lens(dom::Polynomial, cod::Polynomial, on_pos_fn::Function, on_dir_fn::Function)
    on_pos = PolyFunction(dom.positions, cod.positions, on_pos_fn)
    on_dir = DependentFunction(
        dom.positions,
        i -> ExpSet(direction_at(dom, i), direction_at(cod, on_pos_fn(i))),
        i -> PolyFunction(direction_at(cod, on_pos_fn(i)),
                          direction_at(dom, i),
                          b -> on_dir_fn(i, b))
    )
    Lens(dom, cod, on_pos, on_dir)
end

# Identity ----------------------------------------------------------

"""
    identity_lens(p::Polynomial) -> Lens

The identity lens `id_p : p → p`.
"""
function identity_lens(p::Polynomial)
    Lens(p, p,
         PolyFunction(p.positions, p.positions, identity),
         DependentFunction(
             p.positions,
             i -> ExpSet(direction_at(p, i), direction_at(p, i)),
             i -> PolyFunction(direction_at(p, i), direction_at(p, i), identity)
         ))
end

# Composition (vertical) -------------------------------------------

"""
    compose(f::Lens, g::Lens) -> Lens

Vertical composition `f ⨟ g : dom(f) → cod(g)`. Requires `cod(f) == dom(g)`.

On positions: `(f ⨟ g)₁ = f₁ ⨟ g₁`.
On directions: `(f ⨟ g)♯_i = f♯_i ∘ g♯_{f₁ i}` (apply `g♯` first, then `f♯` —
the reverse direction makes sense because both go backward).

Per Niu & Spivak Exercise 3.49 / Proposition 3.50.
"""
function compose(f::Lens, g::Lens)
    f.cod == g.dom || error("Cannot compose: cod(f) = $(f.cod) ≠ dom(g) = $(g.dom)")
    p, _, r = f.dom, f.cod, g.cod

    h_on_pos_fn = i -> g.on_positions.f(f.on_positions.f(i))

    h_on_dir = DependentFunction(
        p.positions,
        i -> ExpSet(direction_at(p, i), direction_at(r, h_on_pos_fn(i))),
        i -> begin
            j = f.on_positions.f(i)
            f_sharp_i = f.on_directions.f(i)::PolyFunction
            g_sharp_j = g.on_directions.f(j)::PolyFunction
            PolyFunction(direction_at(r, h_on_pos_fn(i)),
                         direction_at(p, i),
                         b -> f_sharp_i.f(g_sharp_j.f(b)))
        end
    )

    Lens(p, r,
         PolyFunction(p.positions, r.positions, h_on_pos_fn),
         h_on_dir)
end

# Operator forms.
const var"⨟" = compose
Base.:∘(g::Lens, f::Lens) = compose(f, g)

# Equality ----------------------------------------------------------

"""
Two lenses are equal iff (a) their domains and codomains agree, (b) their
on-positions functions are extensionally equal, and (c) their on-directions
functions agree at every position.
"""
function ==(f::Lens, g::Lens)
    f.dom == g.dom || return false
    f.cod == g.cod || return false
    f.on_positions == g.on_positions || return false
    p = f.dom
    p.positions isa FinPolySet || error("Lens equality requires a FinPolySet position-set.")
    for i in p.positions
        fi = f.on_directions.f(i)::PolyFunction
        gi = g.on_directions.f(i)::PolyFunction
        fi == gi || return false
    end
    true
end

# Apply as a natural transformation -------------------------------

"""
    (f::Lens)(X::PolySet) -> PolyFunction

The X-component `f_X : dom(X) → cod(X)` of the lens viewed as a natural
transformation (Niu & Spivak Proposition 3.44):

    (i, g : dom[i] → X)  ↦  (f₁ i, f♯_i ⨟ g : cod[f₁ i] → X)
"""
function (f::Lens)(X::PolySet)
    domX = f.dom(X)
    codX = f.cod(X)
    PolyFunction(domX, codX, ig -> begin
        (i, g) = ig
        j = f.on_positions.f(i)
        f_sharp_i = f.on_directions.f(i)::PolyFunction
        if g isa AbstractDict
            cod_dir = direction_at(f.cod, j)
            cod_dir isa FinPolySet || error("Expected finite codomain direction-set; got $(typeof(cod_dir))")
            new_g = Dict(b => g[f_sharp_i.f(b)] for b in cod_dir.elements)
            (j, new_g)
        else
            (j, b -> g(f_sharp_i.f(b)))
        end
    end)
end

# Lens count --------------------------------------------------------

"""
    lens_count(p::Polynomial, q::Polynomial) -> Cardinality

The cardinality of `Poly(p, q)` via `Π_{i ∈ p(1)} |q(p[i])|`. Uses
[`cardinality_of_apply`](@ref) — works for symbolic inputs without enumeration.
"""
function lens_count(p::Polynomial, q::Polynomial)
    pos = p.positions
    if !(pos isa FinPolySet)
        return SymbolicCardinality(Symbol("|Poly(", sprint(show, p), ", ", sprint(show, q), ")|"))
    end
    isempty(pos.elements) && return Finite(1)
    reduce(*, (cardinality_of_apply(q, direction_at(p, i)) for i in pos))
end

# ASCII polybox renderer -------------------------------------------

"""
    polybox(f::Lens; entries=nothing) -> String

Render the lens `f` as an ASCII polybox picture. If `entries` is given as a
`(i, b)` pair, the picture is drawn with `p`'s position set to `i`, `q`'s
position set to `f₁ i`, `q`'s direction set to `b`, and `p`'s direction set to
`f♯_i b`.
"""
function polybox(f::Lens; entries=nothing)
    p, q = f.dom, f.cod
    pos_p = "p(1)"
    dir_p = "p[−]"
    pos_q = "q(1)"
    dir_q = "q[−]"

    cells_p_dir, cells_p_pos = "      ", "      "
    cells_q_dir, cells_q_pos = "      ", "      "
    if entries !== nothing
        i, b = entries
        j = f.on_positions.f(i)
        a = f.on_directions.f(i).f(b)
        cells_p_pos = lpad(string(i), 6)
        cells_q_pos = lpad(string(j), 6)
        cells_q_dir = lpad(string(b), 6)
        cells_p_dir = lpad(string(a), 6)
    end

    io = IOBuffer()
    println(io, "                       f♯")
    println(io, "          ", dir_p, lpad(cells_p_dir, 8), "  ←──  ", dir_q, lpad(cells_q_dir, 8))
    println(io, "          ", pos_p, lpad(cells_p_pos, 8), "  ──→  ", pos_q, lpad(cells_q_pos, 8))
    println(io, "                       f₁")
    println(io, "             ", sprint(show, p), "          ", sprint(show, q))
    String(take!(io))
end

function show(io::IO, f::Lens)
    print(io, "Lens(")
    show(io, f.dom)
    print(io, " → ")
    show(io, f.cod)
    print(io, ")")
end

show(io::IO, ::MIME"text/plain", f::Lens) = print(io, polybox(f))
