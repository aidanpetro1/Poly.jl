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
Mutate via [`set_tabulate_cap!`](@ref); reading via `TABULATE_SIZE_CAP[]`
is still supported.
"""
const TABULATE_SIZE_CAP = Ref{Int}(10^5)

"""
    set_tabulate_cap!(n::Int) -> Int

Set the global [`TABULATE_SIZE_CAP`](@ref) and return the previous value.
Use this in scripts that legitimately need to operate on larger domains
than the default `10^5`. Prefer `force=true` on a single `tabulate` call
when raising the cap globally would be too coarse.
"""
function set_tabulate_cap!(n::Int)
    n ≥ 0 || throw(ArgumentError("set_tabulate_cap!: cap must be nonnegative; got $n"))
    old = TABULATE_SIZE_CAP[]
    TABULATE_SIZE_CAP[] = n
    old
end

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
    if !force && c.n > TABULATE_SIZE_CAP[]
        error("""
              Domain has $(c.n) elements (> TABULATE_SIZE_CAP[] = $(TABULATE_SIZE_CAP[])).

              Options to proceed:
                1. Pass `force = true` to tabulate this function anyway.
                2. Raise the global cap: `Poly.set_tabulate_cap!($(c.n) + 1)`
                   (or to whatever ceiling fits the workload).
                3. If you're comparing two functions for equality, see whether a
                   structural predicate fits — e.g. `is_subst_of` for substitution
                   polynomials avoids enumeration entirely.
                4. Build the function manually as a `Dict`-backed `PolyFunction`
                   and pass it directly, skipping tabulation.
              """)
    end
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
    if ca isa Finite && ca.n ≤ TABULATE_SIZE_CAP[]
        if a.dom isa FinPolySet
            return all(x -> a.f(x) == b.f(x), a.dom)
        end
        # `a.dom` may be a lazy variant of a finite-cardinality position-set
        # (e.g. `SubstPolySet` after the v0.4.x `Lens.dom` widening). Iterate
        # by materializing once. Cost is `Σ_i |q.positions|^|p[i]|` jbar
        # construction — the same a fully-eager pre-widening Lens would have
        # paid; only fires when extensional `PolyFunction ==` is requested
        # against a lazy dom.
        elts = _materialize_polyset_elements(a.dom)
        elts === nothing && error(
            "Cannot iterate PolyFunction.dom of type $(typeof(a.dom)); " *
            "add a `_materialize_polyset_elements` method.")
        return all(x -> a.f(x) == b.f(x), elts)
    end
    error("Cannot decide PolyFunction equality: domain not finite, or above TABULATE_SIZE_CAP. " *
          "Tabulate or compare structurally.")
end

# Hook for iterating non-`FinPolySet` finite-cardinality position-sets in
# extensional `PolyFunction ==`. Returns `nothing` if no materialization
# strategy is known. The `SubstPolySet` method is added in `Monoidal.jl`
# (forward-reference issue at file-include time).
_materialize_polyset_elements(::PolySet) = nothing

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
