# # Dynamical systems
#
# In the polynomial-functor picture, a (dependent) dynamical system is a lens
# `φ : Sy^S → p`. The on-positions function is the *return* (output at each
# state); the on-directions function is the *update* (next state given the
# current state and a chosen direction).
#
# A Moore machine is the special case where `p = Iy^A`: every state takes the
# same input set `A` and emits an `I`-valued output.

using Poly

# ## A small Moore machine
#
# Three states, two inputs, two outputs, picked so the output trajectory has a
# recognizable pattern from a known input sequence.

S = FinPolySet([:l, :r, :b])
A = FinPolySet([:o, :g])
I = FinPolySet([0, 1])

return_fn = s -> s == :l ? 0 : 1
update_fn = (s, a) -> begin
    if s == :l
        a == :o ? :l : :r
    elseif s == :r
        a == :o ? :l : :b
    else
        a == :o ? :l : :b
    end
end

φ = moore_machine(S, I, A, return_fn, update_fn)

# Confirm `φ.dom` really is the state system:

is_state_system(φ.dom)

# ## Stepping
#
# `step(φ, state, direction)` advances by one. (It's a method on `Base.step`
# rather than a fresh export, so `step(0:5)` for ranges still works.)

step(φ, :b, :o), step(φ, :l, :g)

# ## Trajectories
#
# Three flavors:
#
# * `trajectory(φ, s0, inputs)` — the list of states visited.
# * `output_trajectory(φ, s0, inputs)` — the outputs emitted along the way.
# * `state_output_trajectory(φ, s0, inputs)` — pairs `(state, output)`.
#
# All three include the initial state, so length is `length(inputs) + 1`.

inputs = [:o, :o, :g, :o]
trajectory(φ, :b, inputs)
#-
output_trajectory(φ, :b, inputs)

# ## A counter
#
# `moore_machine` works with any `PolySet`. Here's a counter mod 6, where
# every state outputs itself.

N = FinPolySet(0:5)
counter = moore_machine(N, N, FinPolySet([:tick]),
                        n -> n,
                        (n, _) -> n == 5 ? 0 : n + 1)
output_trajectory(counter, 0, fill(:tick, 6))

# ## Juxtaposition
#
# Running two systems in parallel is just `juxtapose(φ, ψ)` — an alias for the
# parallel product `φ ⊗ ψ` on lenses. State-set is the cartesian product;
# inputs come in as pairs.

fwd = moore_machine(N, N, FinPolySet([:t]),
                    n -> n, (n, _) -> n == 5 ? 0 : n + 1)
bwd = moore_machine(N, N, FinPolySet([:t]),
                    n -> n, (n, _) -> n == 0 ? 5 : n - 1)
pair = juxtapose(fwd, bwd)
trajectory(pair, (0, 0), [(:t, :t), (:t, :t), (:t, :t)])

# ## Initial-state lens
#
# The `y → Sy^S` lens that picks an initial state. Composing this with `φ`
# gives a closed system `y → p`.

init = initial_state(N, 0)
init.dom, init.cod

# ## Dependent interfaces
#
# `dynamical_system` is the general form — the interface polynomial `p` need
# not be monomial. Different states can have different available actions.

interface = Polynomial(FinPolySet([:running, :final]),
                       i -> i == :running ? A : FinPolySet(Symbol[]))
T = FinPolySet([:s0, :s1, :final])
ret = s -> s == :final ? :final : :running
upd = (s, a) -> begin
    s == :final && error("vacuous: no directions in :final")
    a == :o ? (s == :s0 ? :s1 : :final) : :s0
end
φd = dynamical_system(T, interface, ret, upd)
output_trajectory(φd, :s0, [:o, :o])
