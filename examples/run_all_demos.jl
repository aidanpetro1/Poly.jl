# Run every `_sprintN_demo()` in sequence. These are human-readable
# acceptance demos kept alongside the unit tests; they double as living
# documentation. The CI test suite is `test/runtests.jl`; run that for
# programmatic verification.
#
# Usage (from the package root):
#
#     julia --project=. examples/run_all_demos.jl

include(joinpath(@__DIR__, "..", "src", "Poly.jl"))

Poly._sprint1_demo()
Poly._sprint2_demo()
Poly._polish_demo()
Poly._symbolic_demo()
Poly._sprint3_demo()
Poly._refinement_demo()
Poly._sprint4_demo()
Poly._sprint5_demo()
Poly._sprint6_demo()
Poly._sprint7_demo()
Poly._sprint8_demo()
