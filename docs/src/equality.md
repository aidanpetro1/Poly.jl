# Equality and `≈`

There are three notions of "the same polynomial" in Poly.jl, and they are not interchangeable.

## `==` — strict structural

Same position-set elements, same direction-set per position. Most book identities **fail** under `==`:

```julia
p = @poly y^2
q = @poly y^2
p == q                # true — same construction
p × q == q × p        # false — position-tuples come out in a different order
p × q ≈ q × p         # true — same up to iso
```

## `≈` — cardinality-iso

Alias for `is_iso(p, q)`. True when the position-sets have the same cardinality and the multiset of direction-set cardinalities matches. This is what the book usually means by "the same".

Use `≈` for book identities (commutativity, distributivity, unitor laws).

## `is_iso_strict` — bijection respecting direction-sets

Stricter than `≈`: requires a bijection of positions that maps direction-sets exactly (not just to ones of equal cardinality). Distinguishes `Ny` from `Ry` (both have countably many direction-sets of size 1, but the underlying sets differ).

## Lens equality

`==` on lenses is extensional: same dom, same cod, on-positions and on-directions agree at every input. There is no separate `is_iso` for lenses — for those, the right notion is "same up to invertible whiskering," which is more involved.

## Symbolic equality

`SymbolicPolynomial` `==` and `hash` use commutative-canonicalization (sorted args by string-key), so `a + b == b + a` and `parallel(a, b) == parallel(b, a)`. For full rule-based equality use `sym_equal(a, b)`, which `simplify`s both sides and compares.
