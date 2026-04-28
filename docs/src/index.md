# Poly.jl

A Julia library for **polynomial functors** in the categorical sense. Implements polynomials `p ≅ Σ_{i ∈ p(1)} y^{p[i]}`, dependent lenses, the four monoidal products, dynamical systems, and the Ahman–Uustalu correspondence between comonoids in `(Poly, y, ◁)` and small categories.

Follows Niu and Spivak's *Polynomial Functors: A Mathematical Theory of Interaction* (2024).

## Where to start

If you're new, read the [Quick start](quickstart.md) first, then walk through the tours:

1. [Polynomials and lenses](tours/01_polynomials_and_lenses.md) — what they are, how to build them, the polybox picture.
2. [Dynamical systems](tours/02_dynamical_systems.md) — Moore machines, trajectories, juxtaposition.
3. [Comonoids = categories](tours/03_comonoids_are_categories.md) — Ahman–Uustalu in code.

If you're already familiar with the book, the [API reference](api.md) is the fastest way in.

## Visualization

The sibling package `PolyViz` renders polynomials, lenses, and Moore machines as SVG using Luxor. See `PolyViz/README.md` (when present) or `PolyViz/demo.jl` for end-to-end examples.

## Status

All seven implemented sprints are documented in the [README](https://github.com/aidanpetrovich/Polynomial/blob/main/README.md). Sprint 8 (cofree comonoid `T_p`, comodules, bicomodules) is the next major addition.
