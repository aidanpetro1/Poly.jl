# ============================================================
# PolyFunction (lazy by default, tabulatable)
# ============================================================

"""
    PolyFunction(dom, cod, f)

A function `dom → cod` between two `PolySet`s, stored lazily as a Julia callable.
Use [`tabulate`](@ref) to materialize it as a lookup table when both ends are
finite. Use [`untabulate`](@ref) to go back to the lazy form.

Equality between two `PolyFunction`s falls back to extensional comparison: if
both domains are finite under the soft size cap, every input is checked;
otherwise the comparison errors with a clear message.
"""
mutable struct PolyFunction
    dom::PolySet
    cod::PolySet
    f::Function
    table::Union{Nothing,Dict}
end
PolyFunction(dom, cod, f) = PolyFunction(dom, cod, f, nothing)

(pf::PolyFunction)(x) = pf.table === nothing ? pf.f(x) : pf.table[x]

"""
    TABULATE_SIZE_CAP :: Ref{Int}

The maximum domain size at which a `PolyFunction` will be tabulated or
compared extensionally without an explicit opt-in. Defaults to `10^5`.
Mutate the `[]` slot to raise or lower the cap globally.
"""
const TABULATE_SIZE_CAP = Ref{Int}(10^5)

"""
    tabulate(pf::PolyFunction; force=false) -> PolyFunction

Materialize `pf` as a lookup table. Requires `pf.dom` to be finite and below
[`TABULATE_SIZE_CAP`](@ref) unless `force=true`.
"""
function tabulate(pf::PolyFunction; force=false)
    pf.table !== nothing && return pf
    c = cardinality(pf.dom)
    c isa Finite || error("Cannot tabulate function with non-finite domain (cardinality $c). " *
                          "Pass force=true if you really mean to enumerate it.")
    !force && c.n > TABULATE_SIZE_CAP[] &&
        error("Domain has $(c.n) elements (> TABULATE_SIZE_CAP[] = $(TABULATE_SIZE_CAP[])). " *
              "Pass force=true to override.")
    pf.dom isa FinPolySet ||
        error("Tabulation only supported for FinPolySet domains; got $(typeof(pf.dom)).")
    pf.table = Dict(x => pf.f(x) for x in pf.dom)
    pf
end

"Drop a tabulation, reverting to lazy evaluation through the closure."
function untabulate(pf::PolyFunction)
    pf.table = nothing
    pf
end

function ==(a::PolyFunction, b::PolyFunction)
    a.dom == b.dom || return false
    a.cod == b.cod || return false
    a.f === b.f && return true
    ca = cardinality(a.dom)
    if ca isa Finite && ca.n ≤ TABULATE_SIZE_CAP[] && a.dom isa FinPolySet
        return all(x -> a.f(x) == b.f(x), a.dom)
    end
    error("Cannot decide PolyFunction equality: domain not finite, or above TABULATE_SIZE_CAP. " *
          "Tabulate or compare structurally.")
end

function show(io::IO, pf::PolyFunction)
    print(io, "PolyFunction(")
    show(io, pf.dom)
    print(io, " → ")
    show(io, pf.cod)
    if pf.table !== nothing
        print(io, ", tabulated[", length(pf.table), "])")
    else
        print(io, ", lazy)")
    end
end

# Combinators
"""
    identity_polyfunction(s::PolySet) -> PolyFunction

The identity `PolyFunction` on `s` — domain and codomain both `s`,
underlying function is Julia's `identity`.
"""
identity_polyfunction(s::PolySet) = PolyFunction(s, s, identity)
function compose(f::PolyFunction, g::PolyFunction)
    f.cod == g.dom || error("Cannot compose: codomain $(f.cod) ≠ domain $(g.dom)")
    PolyFunction(f.dom, g.cod, x -> g.f(f.f(x)))
end

# ============================================================
# DependentFunction — for indexed families i ↦ p[i]
# ============================================================

"""
    DependentFunction(dom, cod_at, f)

A dependent function `(i ∈ dom) → cod_at(i)`. `cod_at` is a Julia callable that
maps each element of `dom` to a `PolySet` (the codomain at that index). `f`
maps each `i ∈ dom` to an element of `cod_at(i)`.

This is the type of [`direction_at`](@ref) and of on-directions
maps for lenses.
"""
struct DependentFunction
    dom::PolySet
    cod_at::Function
    f::Function
end
(df::DependentFunction)(i) = df.f(i)

"Build a DependentFunction whose `f` is the identity on PolySets — for direction-set families."
indexed_family(dom::PolySet, cod_at::Function) = DependentFunction(dom, cod_at, cod_at)

show(io::IO, df::DependentFunction) = (print(io, "DependentFunction("); show(io, df.dom); print(io, " → ...)"))
