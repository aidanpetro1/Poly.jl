# ============================================================
# Validation result types (Extensions v1, PR #6)
# ============================================================
#
# `validate_*` functions return a `ValidationResult` with structural
# information about any failures. Existing call sites that expect a `Bool`
# keep working via `Base.convert(::Type{Bool}, ::ValidationResult)`.
#
# Each `ValidationFailure` carries a structural hint — a short human
# description of *why* the law failed, naming the offending sub-component
# (e.g. "duplicator's on-positions disagrees with eraser at $X") rather
# than just reporting which numbered law tripped.

"""
    ValidationFailure(law, location, structural_hint, actual, expected)

A single law violation in a comonoid / comodule / bicomodule / retrofunctor.

  - `law :: Symbol` — the law that failed, e.g. `:counit_left`,
    `:counit_right`, `:coassoc`, `:compatibility_positions`, etc.
  - `location :: Tuple` — the `(object, direction, ...)` tuple where the
    failure was first detected.
  - `structural_hint :: String` — a one-line description of *why* the law
    failed in structural terms, naming the sub-component(s) involved.
  - `actual` — the value the validator computed.
  - `expected` — the value the law required.
"""
struct ValidationFailure
    law::Symbol
    location::Tuple
    structural_hint::String
    actual::Any
    expected::Any
end

function show(io::IO, f::ValidationFailure)
    print(io, "ValidationFailure(", f.law, " at ", f.location, ": ",
          f.structural_hint, "; actual=", repr(f.actual),
          ", expected=", repr(f.expected), ")")
end

"""
    ValidationResult(passed, failures=[], summary="")

The result of a `validate_*` call. Truthy when `passed` is true; carries
structural failure information otherwise.

`Base.Bool(::ValidationResult)` returns `passed`, so existing call sites of
the form `if validate_comonoid(c) ... end` continue to work transparently.
For diagnostic detail, inspect `r.failures` directly.

# Constructors

    ValidationResult(true)                                  # successful, no failures
    ValidationResult(false, [failure])                      # one failure
    ValidationResult(false, failures, "human summary")      # multi-failure with summary
"""
struct ValidationResult
    passed::Bool
    failures::Vector{ValidationFailure}
    summary::String
end

ValidationResult(passed::Bool) = ValidationResult(passed, ValidationFailure[], "")
ValidationResult(passed::Bool, failures::Vector{ValidationFailure}) =
    ValidationResult(passed, failures, "")

Base.Bool(r::ValidationResult) = r.passed
Base.convert(::Type{Bool}, r::ValidationResult) = r.passed
Base.:(!)(r::ValidationResult) = !r.passed
Base.:(==)(r::ValidationResult, b::Bool) = r.passed == b
Base.:(==)(b::Bool, r::ValidationResult) = b == r.passed

function show(io::IO, r::ValidationResult)
    if r.passed
        print(io, "ValidationResult(passed=true")
        isempty(r.summary) || print(io, ", \"", r.summary, "\"")
        print(io, ")")
    else
        print(io, "ValidationResult(passed=false, ", length(r.failures),
              " failure", length(r.failures) == 1 ? "" : "s")
        isempty(r.summary) || print(io, ", \"", r.summary, "\"")
        print(io, ")")
    end
end

function show(io::IO, ::MIME"text/plain", r::ValidationResult)
    if r.passed
        println(io, "ValidationResult: passed")
        isempty(r.summary) || println(io, "  ", r.summary)
        return
    end
    println(io, "ValidationResult: FAILED (", length(r.failures), " failure",
            length(r.failures) == 1 ? "" : "s", ")")
    isempty(r.summary) || println(io, "  ", r.summary)
    for (i, f) in enumerate(r.failures)
        println(io, "  [", i, "] ", f.law, " at ", f.location)
        println(io, "      ", f.structural_hint)
        println(io, "      actual:   ", repr(f.actual))
        println(io, "      expected: ", repr(f.expected))
    end
end

"""
    pass([summary]) -> ValidationResult

Construct a successful `ValidationResult`. Optional human-readable summary.
"""
pass() = ValidationResult(true, ValidationFailure[], "")
pass(summary::AbstractString) = ValidationResult(true, ValidationFailure[], String(summary))

"""
    fail(failure::ValidationFailure; summary="") -> ValidationResult
    fail(failures::Vector{ValidationFailure}; summary="") -> ValidationResult

Construct a failing `ValidationResult`.
"""
fail(failure::ValidationFailure; summary::AbstractString="") =
    ValidationResult(false, [failure], String(summary))
fail(failures::Vector{ValidationFailure}; summary::AbstractString="") =
    ValidationResult(false, failures, String(summary))

"""
    minimal_failing_triple(failures::Vector{ValidationFailure}) -> ValidationFailure

Among `failures` whose `location` is a 3-tuple, return the
lexicographically-smallest one. Useful for `validate_bicomodule` where the
compatibility-square check enumerates `(x, b, a)` triples and the user
benefits from being pointed at the *smallest* failing triple, not just the
first one encountered.

# Worked example

Build an intentionally-broken bicomodule (a right coaction whose direction
map disagrees with the left coaction at one specific triple), validate it
in `:all` mode to collect every failing triple, and use
`minimal_failing_triple` to surface the smallest one for debugging:

```julia
S = FinPolySet([:a, :b])
cs = state_system_comonoid(S)

# A right coaction that lies at one specific (x, b, a) triple, breaking
# direction-level compatibility with the well-formed left coaction.
bad_right_on_dir = (i, ab) -> begin
    a, b = ab
    (i == :a && a == :a && b == :b) ? :a : b
end
bad_right = Lens(cs.carrier, subst(cs.carrier, cs.carrier),
                 s -> (s, Dict(t => t for t in S.elements)),
                 bad_right_on_dir)
B = Bicomodule(cs.carrier, cs, cs, cs.duplicator, bad_right)

# Run validation with `verbose=:all` so every failing triple is recorded,
# not just the first one.
result = validate_bicomodule_detailed(B; verbose=:all)
@assert !result.passed

# Surface the lex-smallest failing (x, b, a) triple for debugging.
worst = minimal_failing_triple(result.failures)
@show worst.law              # :compatibility_directions (or :compatibility_positions)
@show worst.location         # (x, b, a) — the smallest triple that broke
@show worst.structural_hint  # human-readable description of *what* broke
```

Pair this with `result.summary` for a one-line categorical description of
which axiom class failed.
"""
function minimal_failing_triple(failures::Vector{ValidationFailure})
    triples = filter(f -> length(f.location) == 3, failures)
    isempty(triples) && error("minimal_failing_triple: no 3-tuple-location failures present")
    return reduce(triples) do a, b
        # Compare tuples lex; works for any orderable element types.
        try
            a.location < b.location ? a : b
        catch
            # Fallback: compare by repr if elements aren't orderable.
            repr(a.location) < repr(b.location) ? a : b
        end
    end
end
