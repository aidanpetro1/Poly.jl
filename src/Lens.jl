# ============================================================
# Lens (Sprint 2)
# ============================================================

"""
    Lens(dom::Polynomial, cod::AbstractPolynomial,
         on_positions::PolyFunction, on_directions::DependentFunction)

A dependent lens `f : dom → cod` between two polynomials, characterized
(per Niu & Spivak Proposition 3.6) by a pair `(f₁, f♯)`:

- `on_positions :: PolyFunction` — the forward `f₁ : dom(1) → cod(1)`.
- `on_directions :: DependentFunction` — for each `i ∈ dom(1)`, a `PolyFunction`
  `f♯_i : cod[f₁ i] → dom[i]` (note the *reversed* direction).

Lenses are the morphisms of the category **Poly**.

`cod` is typed as `AbstractPolynomial` so that lazy variants
([`LazySubst`](@ref)) can flow through the lens layer without forcing
enumeration. The `dom` remains a [`Polynomial`](@ref) (concrete) because
positions of `dom` are iterated frequently.

Access fields directly: `f.on_positions`, `f.on_directions`.
"""
struct Lens
    dom::Polynomial
    cod::AbstractPolynomial
    on_positions::PolyFunction
    on_directions::DependentFunction
    function Lens(dom::Polynomial, cod::AbstractPolynomial,
                  on_pos::PolyFunction, on_dir::DependentFunction)
        on_pos.dom == dom.positions || error("on_positions domain $(on_pos.dom) ≠ dom.positions $(dom.positions)")
        on_pos.cod == positions(cod) || error("on_positions codomain $(on_pos.cod) ≠ cod.positions $(positions(cod))")
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
function Lens(dom::Polynomial, cod::AbstractPolynomial, on_pos_fn::Function, on_dir_fn::Function)
    cod_pos = positions(cod)
    on_pos = PolyFunction(dom.positions, cod_pos, on_pos_fn)
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
    _struct_equal(f.cod, g.dom) || error("Cannot compose: cod(f) = $(f.cod) ≠ dom(g) = $(g.dom)")
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

    # Use the `positions` accessor on `r` rather than `r.positions`: when
    # `g.cod` is a lazy variant (e.g. `LazySubst`) the field doesn't exist;
    # the accessor is the `AbstractPolynomial` interface contract.
    Lens(p, r,
         PolyFunction(p.positions, positions(r), h_on_pos_fn),
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
    _struct_equal(f.cod, g.cod) || return false
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
    # The cod may be a lazy variant (e.g. LazySubst); materialize-on-demand
    # for the apply path. Lens-as-natural-transformation is rarely on the hot
    # path of bicomodule construction, so paying the materialization cost
    # only when this method is actually called is acceptable.
    cod_concrete = f.cod isa ConcretePolynomial ? f.cod : materialize(f.cod)
    codX = cod_concrete(X)
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

# ============================================================
# back_directions accessor (Extensions v2 PR #6)
# ============================================================
#
# `Lens.on_directions` is a `DependentFunction` that, for each domain
# position `i`, returns a `PolyFunction` mapping codomain directions to
# domain directions (the lens "back-direction" map `f♯_i`). The raw form
# is callable but opaque — you can call it but can't easily enumerate or
# pretty-print it. `back_directions` materializes the map into a
# `BackDirectionTable` (when finite-and-small) for inspection / debugging.

"""
    BackDirectionTable

Materialized view of a `Lens`'s back-direction map: a `Dict`-like wrapper
keyed by `(domain_position, codomain_direction)` with values
`domain_direction`. Returned by [`back_directions`](@ref) when the
underlying data is finite and within `TABULATE_SIZE_CAP`.
"""
struct BackDirectionTable
    entries::Dict{Tuple,Any}
end

Base.getindex(t::BackDirectionTable, key::Tuple) = t.entries[key]
Base.getindex(t::BackDirectionTable, pos, codir) = t.entries[(pos, codir)]
Base.length(t::BackDirectionTable) = length(t.entries)
Base.iterate(t::BackDirectionTable, state...) = iterate(t.entries, state...)
Base.pairs(t::BackDirectionTable) = pairs(t.entries)
Base.haskey(t::BackDirectionTable, key) = haskey(t.entries, key)
Base.keys(t::BackDirectionTable) = keys(t.entries)
Base.values(t::BackDirectionTable) = values(t.entries)
Base.:(==)(a::BackDirectionTable, b::BackDirectionTable) = a.entries == b.entries

function show(io::IO, t::BackDirectionTable)
    print(io, "BackDirectionTable(", length(t.entries), " entries)")
end

function show(io::IO, ::MIME"text/plain", t::BackDirectionTable)
    println(io, "BackDirectionTable (", length(t.entries), " entries):")
    by_pos = Dict()
    for ((p, c), d) in t.entries
        get!(() -> Dict(), by_pos, p)[c] = d
    end
    sorted_pos = try
        sort!(collect(keys(by_pos)))
    catch
        sort!(collect(keys(by_pos)); by=repr)
    end
    for p in sorted_pos
        println(io, "  ", repr(p), ":")
        sub = by_pos[p]
        sorted_codir = try
            sort!(collect(keys(sub)))
        catch
            sort!(collect(keys(sub)); by=repr)
        end
        for c in sorted_codir
            println(io, "    ", repr(c), "  ↦  ", repr(sub[c]))
        end
    end
end

"""
    back_directions(L::Lens; materialize=:auto) -> Union{BackDirectionTable, Function}

Expose the back-direction map of a `Lens`. `materialize` modes: `:auto`
(default, cap-aware), `true` (force, error if over cap), `false`
(callable). When a callable is returned, it has signature
`(pos, codir) -> domdir`.
"""
function back_directions(L::Lens; materialize::Union{Bool,Symbol}=:auto)
    materialize isa Symbol && materialize !== :auto &&
        throw(ArgumentError("back_directions: `materialize` must be :auto, true, or false; got :$materialize"))

    callable = (pos, codir) -> L.on_directions.f(pos).f(codir)

    materialize === false && return callable

    dom_pos = L.dom.positions
    if !(dom_pos isa FinPolySet)
        materialize === true &&
            throw(ArgumentError("back_directions: cannot materialize a Lens whose domain positions are non-finite (got $(typeof(dom_pos)))"))
        return callable
    end

    total = 0
    for i in dom_pos.elements
        codir = direction_at(L.cod, L.on_positions.f(i))
        if !(codir isa FinPolySet)
            materialize === true &&
                throw(ArgumentError("back_directions: cod direction-set at position $(repr(L.on_positions.f(i))) is non-finite (got $(typeof(codir)))"))
            return callable
        end
        total += length(codir.elements)
    end

    if total > TABULATE_SIZE_CAP[]
        materialize === true &&
            error("""back_directions: would materialize $total entries (> TABULATE_SIZE_CAP[] = $(TABULATE_SIZE_CAP[])).
                    Options:
                      1. Pass `materialize=false` to get the (pos, codir) -> domdir callable.
                      2. Raise the global cap: `Poly.set_tabulate_cap!($total + 1)`.""")
        return callable
    end

    entries = Dict{Tuple,Any}()
    for i in dom_pos.elements
        codir = direction_at(L.cod, L.on_positions.f(i))::FinPolySet
        for b in codir.elements
            entries[(i, b)] = L.on_directions.f(i).f(b)
        end
    end
    BackDirectionTable(entries)
end
