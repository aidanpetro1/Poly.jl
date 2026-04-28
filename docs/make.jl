# Build the Poly.jl documentation site.
#
#   julia --project=. setup.jl   # one-time
#   julia --project=. make.jl    # render

using Pkg
Pkg.activate(@__DIR__)

using Documenter
using Literate
using Poly

const DOCS_ROOT = @__DIR__
const LITERATE_SRC = joinpath(DOCS_ROOT, "literate")
const TOURS_OUT   = joinpath(DOCS_ROOT, "src", "tours")
const REPO   = "github.com/aidanpetro1/Poly.jl"
const ON_CI  = get(ENV, "CI", "false") == "true"

isdir(TOURS_OUT) || mkpath(TOURS_OUT)

# Render Literate sources to docs/src/tours/.
if isdir(LITERATE_SRC)
    for f in sort(readdir(LITERATE_SRC))
        endswith(f, ".jl") || continue
        Literate.markdown(joinpath(LITERATE_SRC, f), TOURS_OUT;
                          documenter=true, execute=true)
    end
end

# Locally (no git, no CI), avoid Documenter's edit-link errors by passing
# `remotes=nothing`. On CI, set `repo` so the source-link works.
remote_kwargs = ON_CI ?
    Dict(:repo => "https://$REPO/blob/{commit}{path}#{line}") :
    Dict(:remotes => nothing)

makedocs(;
    sitename  = "Poly.jl",
    authors   = "Aidan Petrovich",
    modules   = [Poly],
    format    = Documenter.HTML(
        prettyurls = ON_CI,
        canonical  = "https://aidanpetro1.github.io/Poly.jl/stable/",
    ),
    checkdocs = :none,
    remote_kwargs...,
    pages = [
        "Home"           => "index.md",
        "Quick start"    => "quickstart.md",
        "Tours" => [
            "Polynomials and lenses"   => "tours/01_polynomials_and_lenses.md",
            "Dynamical systems"        => "tours/02_dynamical_systems.md",
            "Comonoids = categories"   => "tours/03_comonoids_are_categories.md",
            "Monoidal products"        => "tours/04_monoidal_products.md",
            "Closure and derivative"   => "tours/05_closure_and_derivative.md",
            "Cofree and comodules"     => "tours/06_cofree_and_comodules.md",
            "The symbolic layer"       => "tours/07_symbolic_layer.md",
        ],
        "Equality and ≈" => "equality.md",
        "API reference"  => "api.md",
    ],
)

# Deploy to gh-pages on CI; no-op locally.
if ON_CI
    deploydocs(
        repo         = REPO,
        devbranch    = "main",
        push_preview = true,
    )
end
