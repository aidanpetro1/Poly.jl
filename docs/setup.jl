# One-time setup for the docs build.
#
# Run from the docs directory:
#   julia --project=. setup.jl
#
# After this, `julia --project=. make.jl` renders the site to `build/`.

using Pkg
Pkg.activate(@__DIR__)

manifest = joinpath(@__DIR__, "Manifest.toml")
if isfile(manifest)
    println("Removing stale Manifest.toml...")
    rm(manifest)
end

println("Linking Poly as a development dependency...")
Pkg.develop(path=joinpath(@__DIR__, ".."))

println("Installing Documenter and Literate...")
Pkg.add(["Documenter", "Literate"])

println("\nDocs setup complete.")
println("Run `julia --project=. make.jl` to build the site to docs/build/.")
