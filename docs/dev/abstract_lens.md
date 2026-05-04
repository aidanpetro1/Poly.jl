# AbstractLens — extension contract

## Audience

Anyone writing a `<:AbstractLens` subtype. Canonical case: PolyMarkov.jl's
`MarkovLens`, where the back-action lands in distributions rather than
points.

## The interface

Subtypes MUST implement:

  - `dom(L)::AbstractPolynomial`
  - `cod(L)::AbstractPolynomial`
  - `on_positions(L)` — forward action representation (subtype-specific).
  - `on_directions(L)` — back-action representation (subtype-specific).
  - `is_deterministic(L)::Bool`

`Lens` itself implements all five trivially via field access. The
accessors are additive on top of `Lens`'s direct-field-access
contract — existing code using `f.on_positions` etc. continues to work.

## What you do NOT inherit

`compose`, `parallel`, `subst`, `*`, `+`, `▷`, `⊙`, `back_directions`,
`polybox`, `lift`, etc. are defined on `::Lens` specifically. Subtypes
must define their own methods on their own type. Mixed-type calls
require explicit conversion in user code.

This is deliberate: the implementation of `compose` for a stochastic
lens is structurally different (Kleisli bind on directions, not
function composition). The abstract type buys signature compatibility
and a documented interface, not free implementations. Refactoring
those bodies to dispatch on `::AbstractLens` is out of scope until
polymorphism over multiple lens kinds becomes useful (v0.7+).

## Coercion convention

Subtypes that are stronger than `Lens` (carry strictly more
information) provide a downcoercion:

  - `to_lens(M)::Lens` — errors if `!is_deterministic(M)`.

Subtypes that are weaker provide a lift:

  - `to_<subtype>(L::Lens)` — e.g. PolyMarkov's `to_markov(::Lens)`
    wraps each back-direction in a point-mass distribution.

Subtype authors are expected to follow this convention where the
categorical relationship justifies it.

## Field access vs accessor functions

`Lens` documents direct field access (`f.on_positions`) as the public
interface. Accessor functions are the additive abstract entry point.

Rule of thumb: write code against the accessors when it should work on
any `AbstractLens`; field access is fine when you specifically have a
`::Lens`.

## Worked example

See `examples/abstract_lens_minimum_viable.jl` — a
`IdentityLensWrapper <: AbstractLens` exercising all five interface
functions end-to-end.

## Cross-reference

  - `src/Lens.jl` — `AbstractLens` and `Lens` definitions.
  - `src/Polynomial.jl` — the `AbstractPolynomial` pattern this mirrors.
  - PolyMarkov.jl design doc (`docs/dev/polymarkov_handoff.md`) — the
    canonical non-trivial subtype's bridge spec.
