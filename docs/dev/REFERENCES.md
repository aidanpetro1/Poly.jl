# References used by Poly.jl

This file lists the source materials Poly.jl is built on. The materials themselves are not redistributed in this repo (the book is gitignored at the top level) — fetch a copy from the canonical source if you want one alongside your local checkout.

## Primary

**Niu, N. and Spivak, D. I.** *Polynomial Functors: A Mathematical Theory of Interaction.* 2024. Source: <https://github.com/ToposInstitute/poly>. Latest update: 2024-07-17.

Every named definition, theorem, and example in Poly.jl that traces back to this book is annotated with the chapter / equation / example number in its docstring (e.g. "Eq. 4.75", "Example 6.1.3").

If you want the PDF locally for grep purposes, drop `poly-book.pdf` into the repo root — it's already in `.gitignore`.

## Secondary

**Ahman, D. and Uustalu, T.** *Directed Containers as Categories.* 2016. arXiv:1604.01187. The Cat# = Comon(Poly, y, ◁) correspondence implemented in `src/Comonoid.jl` is theirs. Niu/Spivak Chapter 7 cites this as the core source for the equivalence.

## How references are tracked in code

Most Sprint-7+ functions name a specific theorem in their docstring. Use grep when navigating:

```sh
rg "Niu.{0,5}Spivak" src/        # textual references
rg "Ahman" src/                  # the comonoid/category correspondence
rg "Eq\\. \\d|Example \\d|Theorem \\d|Proposition \\d" src/
```

A future version may add formal `[citation]` markers consumable by Documenter or by `CITATION.cff` tooling. For v0.1.0 the inline docstring references are the source of truth.
