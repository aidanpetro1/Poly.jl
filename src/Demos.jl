# ============================================================
# Acceptance demos (human-readable inspection)
# ============================================================
#
# These are kept for human use. The `Test`-based suite under `test/runtests.jl`
# is what CI runs.

"Run the Sprint 1 acceptance demo."
function _sprint1_demo()
    println("== Sprint 1 acceptance demo ==\n")

    pos = FinPolySet([1, 2, 3, 4])
    dir = i -> i == 1 ? FinPolySet([:a1, :a2]) :
                i == 2 || i == 3 ? FinPolySet([:b]) :
                FinPolySet(Symbol[])
    p = Polynomial(pos, dir)
    print("Constructed polynomial: ")
    show(stdout, p)
    println()

    @assert is_monomial(p) == false
    @assert is_constant(p) == false
    @assert is_linear(p) == false
    println("  is_constant=$(is_constant(p)) is_linear=$(is_linear(p)) is_monomial=$(is_monomial(p)) is_representable=$(is_representable(p))")

    X = FinPolySet([:a, :b])
    pX = p(X)
    println("\np(X) for X = ", X, ":")
    println("  cardinality(p(X)) = ", cardinality(pX))
    @assert cardinality(pX) == Finite(9)

    A = SymbolicSet(:A)
    B = SymbolicSet(:B)
    cAB_prod = cardinality(A) * cardinality(B)
    cAB_pow = cardinality(A) ^ cardinality(B)
    println("\nCardinality algebra:")
    println("  |A| × |B| = ", cAB_prod)
    println("  |A| ^ |B| = ", cAB_pow)

    @assert is_constant(zero_poly)
    @assert is_constant(one_poly)
    @assert is_representable(one_poly)
    @assert is_linear(y)
    @assert is_representable(y)

    println("\nCorolla forest of y^2 + 2y + 1:")
    println(corolla_forest(p))

    println("\n== All Sprint 1 acceptance tests passed. ==")
    true
end

"Run the Sprint 2 acceptance demo."
function _sprint2_demo()
    println("\n== Sprint 2 acceptance demo ==\n")

    q = Polynomial(
        FinPolySet([:open, :closed]),
        i -> i == :open ? FinPolySet([:penny, :nickel, :dime, :quarter]) :
                          FinPolySet(Symbol[])
    )
    p = Polynomial(
        FinPolySet([:needy, :greedy, :content]),
        i -> i == :needy   ? FinPolySet([:save, :spend]) :
             i == :greedy  ? FinPolySet([:accept, :reject, :ask_for_more]) :
                             FinPolySet([:count, :rest])
    )
    on_pos = i -> (i == :content) ? :closed : :open
    on_dir = (i, b) -> begin
        if i == :needy
            b == :penny ? :spend : :save
        elseif i == :greedy
            (b == :penny || b == :nickel) ? :ask_for_more : :accept
        else
            error("vacuous")
        end
    end
    f = Lens(p, q, on_pos, on_dir)
    println("Coin-jar / owner lens built: ", f)

    println("\nPolybox at (i=:needy, b=:dime):")
    print(polybox(f; entries=(:needy, :dime)))

    P = Polynomial(
        FinPolySet([1, 2, 3]),
        i -> i == 1 ? FinPolySet([:d1, :d2, :d3]) : FinPolySet([:e])
    )
    Q = Polynomial(
        FinPolySet([1, 2, 3, 4]),
        i -> i == 1 ? FinPolySet([:a, :b, :c, :d]) :
             i == 2 ? FinPolySet([:m, :n]) :
                      FinPolySet(Symbol[])
    )
    n = lens_count(P, Q)
    println("\nlens_count(y^3 + 2y, y^4 + y^2 + 2) = ", n)
    @assert n == Finite(1472)

    id_p = identity_lens(p)
    @assert compose(id_p, id_p) == id_p

    println("\n== All Sprint 2 acceptance tests passed. ==")
    true
end

"Run the Sprint 1+2 polish-pass demo."
function _polish_demo()
    println("\n== Sprint 1+2 polish-pass demo ==\n")

    p1 = Polynomial(FinPolySet([1, 2]), i -> FinPolySet([:a]))
    p2 = Polynomial(FinPolySet([1, 2]), i -> FinPolySet([:a]))
    p3 = Polynomial(FinPolySet([1, 2]), i -> FinPolySet([:b]))
    @assert p1 == p2
    @assert !(p1 == p3)

    owner = Polynomial(
        FinPolySet([:needy, :greedy, :content]),
        i -> i == :needy   ? FinPolySet([:save, :spend]) :
             i == :greedy  ? FinPolySet([:accept, :reject, :ask_for_more]) :
                             FinPolySet([:count, :rest])
    )
    println("Owner merged display:    ", sprint(show, owner))
    println("Owner structural display: ", sprint(show, MIME"text/plain"(), owner))

    q = Polynomial(
        FinPolySet([1, 2, 3, 4]),
        i -> i == 1 ? FinPolySet([:a, :b, :c, :d]) :
             i == 2 ? FinPolySet([:m, :n]) :
                      FinPolySet(Symbol[])
    )
    @assert cardinality_of_apply(q, FinPolySet([1, 2, 3])) == Finite(92)

    Asym, Bsym = SymbolicCardinality(:A), SymbolicCardinality(:B)
    @assert Finite(0) * Asym == Finite(0)
    @assert Asym + Bsym == Bsym + Asym
    @assert Asym * Bsym == Bsym * Asym

    println("\n== All Sprint 1+2 polish tests passed. ==")
    true
end

"Run the Sprint 3 demo: concrete monoidal products and the rewrite rules."
function _sprint3_demo()
    println("\n== Sprint 3 acceptance demo ==\n")

    # Build p = y^3 + y and q = y^4 + y^2 + 1 from Niu & Spivak Example 3.62.
    p = Polynomial(FinPolySet([1, 2]),
                   i -> i == 1 ? FinPolySet([:a, :b, :c]) : FinPolySet([:d]))
    q = Polynomial(FinPolySet([1, 2, 3]),
                   i -> i == 1 ? FinPolySet([:m, :n, :o, :p]) :
                        i == 2 ? FinPolySet([:r, :s]) :
                                 FinPolySet(Symbol[]))
    println("p = ", p)
    println("q = ", q)

    # ---- Coproduct ----
    pq_sum = p + q
    println("\np + q = ", pq_sum)
    @assert is_iso(pq_sum, Polynomial(FinPolySet([1, 2, 3, 4, 5]),
                                       i -> i in (1,) ? FinPolySet([:a, :b, :c]) :
                                            i == 2     ? FinPolySet([:d]) :
                                            i == 3     ? FinPolySet([:m, :n, :o, :p]) :
                                            i == 4     ? FinPolySet([:r, :s]) :
                                                         FinPolySet(Symbol[])))

    # ---- Cartesian product (Example 3.62: y^7 + 2y^5 + 2y^3 + y) ----
    pq_prod = p * q
    println("\np × q = ", pq_prod)
    expected_prod = Polynomial(FinPolySet([1, 2, 3, 4, 5, 6]),
                                i -> i == 1 ? FinPolySet(1:7) :
                                     i == 2 ? FinPolySet(1:5) :
                                     i == 3 ? FinPolySet(1:3) :
                                     i == 4 ? FinPolySet(1:5) :
                                     i == 5 ? FinPolySet(1:3) :
                                              FinPolySet(1:1))
    @assert is_iso(pq_prod, expected_prod) "Example 3.62: y^3+y times y^4+y^2+1 should be y^7+2y^5+2y^3+y"
    println("  matches Example 3.62: y^7 + 2y^5 + 2y^3 + y. ✓")

    # ---- Parallel product (Example 3.70-style: y^12 + y^6 + y^4 + y^2 + 2) ----
    pq_par = parallel(p, q)
    println("\np ⊗ q = ", pq_par)
    # Cardinalities of direction-sets: pairs (3,4), (3,2), (3,0), (1,4), (1,2), (1,0)
    # → products 12, 6, 0, 4, 2, 0 → y^12 + y^6 + 1 + y^4 + y^2 + 1 = y^12+y^6+y^4+y^2+2
    @assert cardinality(pq_par.positions) == Finite(6)
    cards = sort([cardinality(direction_at(pq_par, i)).n for i in pq_par.positions])
    @assert cards == [0, 0, 2, 4, 6, 12] "Example 3.70: ⊗ multiplies direction-set cardinalities"
    println("  matches Example 3.70: y^12 + y^6 + y^4 + y^2 + 2. ✓")

    # ---- Distributivity (Exercise 3.77: (p1 + p2) ⊗ q ≅ (p1 ⊗ q) + (p2 ⊗ q)) ----
    p1 = Polynomial(FinPolySet([:a]), i -> FinPolySet([:x, :y_]))     # y^2
    p2 = Polynomial(FinPolySet([:b]), i -> FinPolySet([:z]))           # y
    qq = Polynomial(FinPolySet([:c]), i -> FinPolySet([:m, :n, :o]))   # y^3
    lhs = parallel(p1 + p2, qq)
    rhs = parallel(p1, qq) + parallel(p2, qq)
    @assert is_iso(lhs, rhs) "Exercise 3.77: ⊗ distributes over +"
    println("\n(p1 + p2) ⊗ q ≅ (p1 ⊗ q) + (p2 ⊗ q): ✓")

    # ---- Symbolic rewrite: distributivity ----
    sa, sb, sc = sympoly(:a), sympoly(:b), sympoly(:c)
    expr_lhs = parallel(sa + sb, sc)
    println("\n(a + b) ⊗ c symbolic: ", expr_lhs)
    println("simplify           : ", simplify(expr_lhs))
    @assert sym_equal(parallel(sa + sb, sc),
                      parallel(sa, sc) + parallel(sb, sc))
    println("sym_equal((a + b) ⊗ c, (a ⊗ c) + (b ⊗ c)): ✓")

    # ---- Symbolic rewrite: 0 absorption ----
    @assert simplify(sa * sym_zero) == sym_zero
    @assert simplify(parallel(sym_zero, sa)) == sym_zero
    println("Zero absorption rules fire: ✓")

    # ---- Commutative canonicalization ----
    @assert (sa + sb) == (sb + sa)
    @assert (sa * sb) == (sb * sa)
    @assert parallel(sa, sb) == parallel(sb, sa)
    println("Commutative canonicalization: a + b == b + a etc. ✓")

    # ---- evaluate(symbolic, env) yields concrete result ----
    env = Dict(:p => p, :q => q)
    @assert evaluate(sympoly(:p) + sympoly(:q), env) == p + q
    @assert is_iso(evaluate(sympoly(:p) * sympoly(:q), env), p * q)
    println("evaluate(symbolic, env) round-trips to concrete: ✓")

    println("\n== All Sprint 3 acceptance tests passed. ==")
    true
end

"""
Run the Sprint 4 demo: composition product `◁`.

The book uses `◁`, but Julia doesn't recognize that as an infix operator;
in code we use `▷` (the closest valid alternative). Display strings and
comments still use `◁` to match the book.
"""
function _sprint4_demo()
    println("\n== Sprint 4 acceptance demo ==\n")

    # Niu & Spivak §6.1.3 example: (y² + y) ◁ (y³ + 1) ≈ y⁶ + 3y³ + 2
    p = @poly y^2 + y
    q = @poly y^3 + 1
    println("p = ", p, ",  q = ", q)

    pq = p ▷ q
    println("\np ◁ q = ", pq)
    @assert cardinality(pq.positions) == Finite(6)
    cards = sort([cardinality(direction_at(pq, i)).n for i in pq.positions])
    @assert cards == [0, 0, 3, 3, 3, 6] "Book §6.1.3 picture: y⁶ + 3y³ + 2"
    println("  direction-set cardinalities (sorted) = ", cards, "  ✓ matches book §6.1.3")

    # ---- Unit laws: p ◁ y ≈ p, y ◁ p ≈ p ----
    @assert (p ▷ y) ≈ p
    @assert (y ▷ p) ≈ p
    println("\nUnit laws: p ◁ y ≈ p, y ◁ p ≈ p ✓")

    # ---- Left distributivity (Prop 6.47): (a + b) ◁ c ≈ (a ◁ c) + (b ◁ c) ----
    a = @poly y^2
    b = @poly y
    c = @poly y + 1
    @assert ((a + b) ▷ c) ≈ ((a ▷ c) + (b ▷ c))
    println("Left distributivity: (a + b) ◁ c ≈ (a ◁ c) + (b ◁ c) ✓")

    # ---- ◁ is NOT right-distributive: r ◁ (p + q) ≠ (r ◁ p) + (r ◁ q) ----
    r = @poly y^2
    lhs = r ▷ (b + b)              # r ◁ (y + y) = y² ◁ 2y
    rhs = (r ▷ b) + (r ▷ b)        # (y² ◁ y) + (y² ◁ y) = 2y²
    @assert !(lhs ≈ rhs)
    println("◁ not right-distributive: r ◁ (p + q) ≢ (r ◁ p) + (r ◁ q) ✓")

    # ---- Constants on the left: 0 ◁ p = 0, 1 ◁ p = 1 ----
    @assert (zero_poly ▷ p) == zero_poly
    @assert (one_poly  ▷ p) ≈ one_poly
    println("Constants under ◁: 0 ◁ p = 0, 1 ◁ p ≈ 1 ✓")

    # ---- Monomial composition: y^A ◁ y^B ≈ y^(|A|·|B|) ----
    yA = @poly y^3
    yB = @poly y^2
    @assert (yA ▷ yB) ≈ (@poly y^6)
    println("Monomial composition: y^3 ◁ y^2 ≈ y^6 ✓")

    # ---- n-fold composition ----
    @assert subst_n(p, 0) ≈ y
    @assert subst_n(p, 1) ≈ p
    @assert subst_n(p, 2) ≈ (p ▷ p)
    println("subst_n: p ◁⁰ = y, p ◁¹ = p, p ◁² = p ◁ p ✓")

    # ---- Symbolic side ----
    sa, sb, sc = sympoly(:a), sympoly(:b), sympoly(:c)
    expr = subst(sa + sb, sc)
    println("\nsymbolic (a + b) ◁ c: ", expr)
    println("simplify           : ", simplify(expr))
    @assert sym_equal(subst(sa + sb, sc),
                      subst(sa, sc) + subst(sb, sc))
    println("sym_equal((a + b) ◁ c, (a ◁ c) + (b ◁ c)): ✓")

    @assert simplify(subst(sym_zero, sa)) == sym_zero
    @assert simplify(subst(sym_one, sa))  == sym_one
    println("0 ◁ a → 0, 1 ◁ a → 1 simplify: ✓")

    println("\n== All Sprint 4 acceptance tests passed. ==")
    true
end

"""
Run the Sprint 5 demo: closure `[q, r]` of `⊗`, sections, derivative,
do-nothing section, evaluation lens.
"""
function _sprint5_demo()
    println("\n== Sprint 5 acceptance demo ==\n")

    # Build small examples. We pick `p` with no constant (empty-direction)
    # summand so Γ(p) > 0 and `section_lens` has something to build from.
    p = @poly y^2 + y
    q = @poly y + 1
    r = @poly y^2

    # ---- internal_hom and the closure adjunction ----
    qr = internal_hom(q, r)
    println("[q, r] for q = ", q, ", r = ", r, ":")
    println("  ", qr)
    # |Poly(q, r)| should equal cardinality of [q, r]'s position-set.
    n_lenses = lens_count(q, r)
    @assert cardinality(qr.positions) == n_lenses
    println("  |[q, r](1)| = ", cardinality(qr.positions),
            " == |Poly(q, r)| = ", n_lenses, " ✓")

    # Closure adjunction: |Poly(p ⊗ q, r)| == |Poly(p, [q, r])|
    lhs = lens_count(parallel(p, q), r)
    rhs = lens_count(p, internal_hom(q, r))
    @assert lhs == rhs
    println("\nClosure adjunction: |Poly(p ⊗ q, r)| = |Poly(p, [q, r])| = ", lhs, " ✓")

    # ---- Niu/Spivak Example 4.81 identities ----
    A = FinPolySet([:a, :b, :c])  # |A| = 3
    yA = representable(A)          # y^A
    Ay = linear(A)                 # Ay
    println("\nExample 4.81 identities (A = ", A, "):")
    # [y^A, y] ≅ Ay
    h1 = internal_hom(yA, y)
    @assert h1 ≈ Ay
    println("  [y^A, y] ≈ Ay ✓")
    # [Ay, y] ≅ y^A
    h2 = internal_hom(Ay, y)
    @assert h2 ≈ yA
    println("  [Ay, y] ≈ y^A ✓")

    # ---- Sections ----
    secs_p = sections(p)
    println("\nsections(", p, "):")
    println("  count = ", cardinality(secs_p),
            "  (= Π_i |p[i]| = ", reduce(*, [cardinality(direction_at(p, i)).n for i in p.positions.elements]; init=1), ")")
    # |Γ(p)| matches Π |p[i]|
    @assert cardinality(secs_p).n ==
            reduce(*, [cardinality(direction_at(p, i)).n for i in p.positions.elements]; init=1)
    println("  |Γ(p)| matches the product formula ✓")

    # Build a section as a lens p → y
    σ = first(secs_p.elements)
    γ = section_lens(p, σ)
    @assert γ.cod == y
    println("  section_lens builds a Lens p → y, cod = ", γ.cod)

    # ---- Do-nothing section on a state system ----
    S = FinPolySet([:s1, :s2, :s3])
    ε = do_nothing_section(S)
    @assert ε.dom == monomial(S, S)
    @assert ε.cod == y
    # ε on directions sends position i to the direction-equal-to-i
    @assert ε.on_directions.f(:s2).f(:pt) == :s2
    println("\nDo-nothing section ε : Sy^S → y on S = ", S, ":")
    println("  ε(s2)(:pt) = ", ε.on_directions.f(:s2).f(:pt), " ✓")

    # ---- Derivative ----
    ṗ = derivative(p)
    println("\nderivative of ", p, " = ", ṗ)
    # Niu/Spivak: ṗ has Σ |p[i]| positions, with cardinalities |p[i]| − 1 each.
    expected_n_positions = sum(cardinality(direction_at(p, i)).n for i in p.positions.elements)
    @assert cardinality(ṗ.positions).n == expected_n_positions
    println("  |ṗ(1)| = ", cardinality(ṗ.positions),
            "  (= Σ |p[i]|, the total directions of p) ✓")

    # ---- Evaluation lens [q, r] ⊗ q → r ----
    ev = eval_lens(q, r)
    @assert ev.dom == parallel(internal_hom(q, r), q)
    @assert ev.cod == r
    println("\neval_lens : [q, r] ⊗ q → r built; dom = ", ev.dom, ", cod = ", ev.cod, " ✓")

    println("\n== All Sprint 5 acceptance tests passed. ==")
    true
end

"""
Run the Sprint 6 demo: dynamical systems as `Sy^S → p` lenses,
including a Moore machine, a counter, and trajectory computation.
"""
function _sprint6_demo()
    println("\n== Sprint 6 acceptance demo ==\n")

    # ---- A small Moore machine ----
    # Three states {:l, :r, :b}, two inputs {:o, :g}, two outputs {0, 1}.
    # Transitions hand-picked so the output trajectory has a recognizable
    # pattern when starting from :b with the input sequence [:o, :o, :g, :o].
    S = FinPolySet([:l, :r, :b])
    A = FinPolySet([:o, :g])
    I = FinPolySet([0, 1])

    return_fn = s -> s == :l ? 0 : 1   # left state outputs 0; others output 1
    update_fn = (s, a) -> begin
        if s == :l
            a == :o ? :l : :r
        elseif s == :r
            a == :o ? :l : :b
        else  # :b
            a == :o ? :l : :b
        end
    end

    φ = moore_machine(S, I, A, return_fn, update_fn)
    println("Moore machine on states ", S, ", inputs ", A, ", outputs ", I)
    println("  φ = ", φ)
    @assert is_state_system(φ.dom)

    # Stepping
    @assert step(φ, :b, :o) == :l
    @assert step(φ, :l, :g) == :r

    # Trajectory & outputs
    inputs = [:o, :o, :g, :o]
    states = trajectory(φ, :b, inputs)
    outs   = output_trajectory(φ, :b, inputs)
    println("\nstart at :b, inputs = ", inputs)
    println("  states  : ", states)
    println("  outputs : ", outs)
    @assert states == [:b, :l, :l, :r, :l]
    @assert outs   == [1, 0, 0, 1, 0]
    println("  output sequence (1, 0, 0, 1, 0) ✓")

    # ---- Initial-state lens ----
    init = initial_state(S, :b)
    @assert init.dom == y
    @assert init.cod == state_system(S)
    @assert init.on_positions.f(:pt) == :b
    println("\ninitial_state(S, :b): y → Sy^S, sends :pt ↦ :b ✓")

    # ---- A counter (1, ℕ)-Moore machine on ℕ ----
    # We use a finite slice of ℕ for the demo.
    N = FinPolySet(0:5)
    counter = moore_machine(N, N, FinPolySet([:tick]),
                            n -> n,
                            (n, _) -> n == 5 ? 0 : n + 1)
    counter_outs = output_trajectory(counter, 0, fill(:tick, 5))
    println("\nCounter from 0 with 5 :tick inputs:")
    println("  outputs = ", counter_outs)
    @assert counter_outs == [0, 1, 2, 3, 4, 5]

    # ---- Juxtaposition ----
    # Run two counters in parallel: one ticking forward, one ticking backward.
    fwd = moore_machine(N, N, FinPolySet([:t]),
                        n -> n, (n, _) -> n == 5 ? 0 : n + 1)
    bwd = moore_machine(N, N, FinPolySet([:t]),
                        n -> n, (n, _) -> n == 0 ? 5 : n - 1)
    pair = juxtapose(fwd, bwd)
    println("\nJuxtaposition: fwd ⊗ bwd (state-set is N×N):")
    println("  dom = ", pair.dom)
    @assert is_state_system(pair.dom)
    # Initial state is (0, 0); each step ticks both clocks.
    pair_states = trajectory(pair, (0, 0), [(:t, :t), (:t, :t), (:t, :t)])
    println("  states = ", pair_states)
    @assert pair_states == [(0, 0), (1, 5), (2, 4), (3, 3)]

    # ---- Wrap an interface ----
    # Wrap the counter through a lens that re-labels its outputs.
    # Simple identity wrap for demonstration.
    iden = identity_lens(monomial(N, FinPolySet([:tick])))
    wrapped = wrap(counter, iden)
    @assert wrapped == counter
    println("\nWrap with id_interface is the identity (wrap(φ, id) == φ): ✓")

    println("\n== All Sprint 6 acceptance tests passed. ==")
    true
end

"""
Run the Sprint 7 demo: comonoids in `(Poly, y, ▷)` are categories
(Ahman–Uustalu). Builds the three canonical comonoids, validates them by
translation to `SmallCategory`, and demonstrates retrofunctors.
"""
function _sprint7_demo()
    println("\n== Sprint 7 acceptance demo ==\n")

    # ---- 1. State-system comonoid: contractible groupoid ----
    S = FinPolySet([:a, :b, :c])
    cs = state_system_comonoid(S)
    println("state_system_comonoid(", S, "): ", cs)

    Cs = to_category(cs)
    println("  as a category: ", Cs)
    @assert cardinality(Cs.objects)   == Finite(3)   # 3 objects
    @assert cardinality(Cs.morphisms) == Finite(9)   # one arrow per (s, t) pair
    @assert validate_comonoid(cs) "state_system_comonoid should satisfy comonoid laws"
    println("  validate_comonoid: ✓")

    # Inspect a morphism: (:a, :b) means a → b. Compose with (:b, :c) to get a → c.
    f = (:a, :b)
    g = (:b, :c)
    @assert Cs.dom[f] == :a && Cs.cod[f] == :b
    @assert Cs.dom[g] == :b && Cs.cod[g] == :c
    @assert Cs.composition[(f, g)] == (:a, :c)
    println("  morphism composition: (a→b) ; (b→c) = (a→c) ✓")
    @assert Cs.identity[:a] == (:a, :a)
    println("  identity at :a is the morphism (a→a) ✓")

    # ---- 2. Discrete comonoid: only identities ----
    cd = discrete_comonoid(S)
    println("\ndiscrete_comonoid(", S, "): ", cd)
    Cd = to_category(cd)
    @assert cardinality(Cd.morphisms) == Finite(3)   # |S| identity morphisms
    @assert validate_comonoid(cd) "discrete_comonoid should satisfy comonoid laws"
    # Every morphism is an identity.
    for m in Cd.morphisms.elements
        @assert Cd.dom[m] == Cd.cod[m]
        @assert Cd.identity[Cd.dom[m]] == m
    end
    println("  validate_comonoid: ✓ (every morphism is an identity)")

    # ---- 3. Monoid comonoid: ℤ/4 under addition ----
    M = FinPolySet(0:3)
    add4 = (a, b) -> mod(a + b, 4)
    cm = monoid_comonoid(M, 0, add4)
    println("\nmonoid_comonoid(ℤ/4, +): ", cm)

    Cm = to_category(cm)
    println("  as a category: ", Cm,
            "  (one-object category BM)")
    @assert cardinality(Cm.objects)   == Finite(1)   # one object :pt
    @assert cardinality(Cm.morphisms) == Finite(4)   # |M| morphisms at that object
    @assert validate_comonoid(cm) "monoid_comonoid(ℤ/4, +) should satisfy comonoid laws"
    println("  validate_comonoid: ✓")
    # The composition table reproduces addition mod 4.
    @assert Cm.composition[((:pt, 1), (:pt, 2))] == (:pt, 3)
    @assert Cm.composition[((:pt, 3), (:pt, 3))] == (:pt, 2)
    println("  composition table = addition mod 4 ✓")

    # ---- 4. A non-monoid catches the laws ----
    # `op(a, b) = a` (left projection) fails associativity? Actually it's
    # associative and has no two-sided identity unless |M| = 1, so it should
    # fail right-identity. Build it and confirm validate fails.
    bad_op = (a, _b) -> a
    cbad = monoid_comonoid(M, 0, bad_op)
    @assert !validate_comonoid(cbad) "left-projection has no right identity → should fail"
    println("\nLeft-projection bad_op fails validate_comonoid: ✓")

    # ---- 5. Round-trip: from_category(to_category(c)) ≅ c ----
    cs_round = from_category(to_category(cs))
    @assert cs_round.carrier == cs.carrier
    @assert validate_comonoid(cs_round)
    println("\nfrom_category ∘ to_category preserves the carrier: ✓")

    # ---- 6. Retrofunctors ----
    id_F = identity_retrofunctor(cs)
    @assert validate_retrofunctor(id_F)
    println("\nIdentity retrofunctor on state_system_comonoid: validate ✓")

    # Compose identity with itself
    id2 = compose(id_F, id_F)
    @assert validate_retrofunctor(id2)
    @assert id2.underlying == id_F.underlying
    println("Composition of identity retrofunctors stays identity: ✓")

    println("\n== All Sprint 7 acceptance tests passed. ==")
    true
end

"""
Run the Sprint 8 demo: depth-bounded cofree comonoid `T_p^{(d)}`,
behavior trees and paths, comodules with the regular comodule on a
small comonoid.
"""
function _sprint8_demo()
    println("\n== Sprint 8 acceptance demo ==\n")

    # ---- Behavior trees on a tiny polynomial ----
    # p = y + 1: one position with one direction (:tick), one constant.
    p = Polynomial(FinPolySet([:run, :halt]),
                   i -> i == :run ? FinPolySet([:tick]) :
                                    FinPolySet(Symbol[]))
    println("p = ", p)

    trees1 = behavior_trees(p, 1)
    println("\nBehavior trees of depth ≤ 1: ", length(trees1))
    for t in trees1
        println("  ", t)
    end
    # depth-0: 2 trees (•run, •halt)
    # depth-1: •run[tick↦•run], •run[tick↦•halt]; •halt is dup
    # total: 4
    @assert length(trees1) == 4

    # Paths through one of them
    t_runs = trees1[findfirst(t -> !isempty(t.children), trees1)]
    println("\nPaths through ", t_runs, ": ", tree_paths(t_runs))
    @assert length(tree_paths(t_runs)) == 2  # () and (:tick,)

    # ---- The cofree comonoid at depth 2 ----
    Tp = cofree_comonoid(p, 2)
    println("\ncofree_comonoid(p, 2): ", Tp)
    println("  carrier has ", cardinality(Tp.carrier.positions), " positions (= trees up to depth 2)")
    @assert validate_comonoid(Tp)
    println("  validate_comonoid: ✓")
    @assert validate_comonoid(Tp; mode=:lens)
    println("  validate_comonoid(mode=:lens): ✓")

    # As a category: paths through trees compose by concatenation, identity is empty path.
    C_T = to_category(Tp)
    println("  ", C_T)
    # Pick any tree with a non-empty path and verify composition is concatenation
    let m = first(t for t in C_T.morphisms.elements if !isempty(t[2]))
        i = C_T.dom[m]
        # compose with the identity at cod → should give back m
        id_cod = C_T.identity[C_T.cod[m]]
        @assert C_T.composition[(m, id_cod)] == m
    end
    println("  identity-right law on a non-trivial path: ✓")

    # ---- Comodules ----
    # The regular comodule on the state-system comonoid: validates iff the
    # comonoid laws hold on the underlying comonoid. We've already shown
    # state_system_comonoid is well-formed.
    S = FinPolySet([:a, :b, :c])
    cs = state_system_comonoid(S)
    M = regular_right_comodule(cs)
    println("\nregular_comodule(state_system_comonoid(", S, ")): ", M)
    @assert validate_right_comodule(M)
    println("  validate_right_comodule: ✓")

    # Cofree comonoid is itself a comonoid, so it has a regular comodule too.
    M_T = regular_right_comodule(Tp)
    @assert validate_right_comodule(M_T)
    println("  regular_right_comodule(cofree_comonoid(p, 2)) validates: ✓")

    # ---- RightComodule constructor catches mismatched coactions ----
    # Try a coaction that doesn't satisfy first-component law.
    bogus = Lens(cs.carrier, subst(cs.carrier, cs.carrier),
                 # send every position to (a, jbar) — wrong first component for b, c
                 _ -> (:a, Dict(t => t for t in S.elements)),
                 (_, ab) -> ab[2])
    bogus_M = RightComodule(cs.carrier, cs, bogus)
    @assert !validate_right_comodule(bogus_M)
    println("\nDeliberately-bogus coaction (wrong first component) fails validate_right_comodule: ✓")

    # ---- Cofree universal property ----
    # The state-system comonoid on S has its own labeling lens to the
    # representable y^S — we'll use cs.eraser-shaped data to make a labeling
    # to the simple polynomial p above. For demo purposes we use the labeling
    # that drops every state to :run if it has any direction, :halt otherwise
    # — but cs.carrier = Sy^S has S directions per state, so every state
    # labels to :run.
    S = FinPolySet([:s1, :s2])
    cs = state_system_comonoid(S)
    labeling = Lens(cs.carrier, p, _ -> :run, (_i, _a) -> S.elements[1])
    F = cofree_universal(cs, labeling, 2)
    # The truncated retrofunctor doesn't satisfy validate_retrofunctor
    # in either strict or non-strict mode — see cofree_universal's
    # docstring. The universal property is checked element-wise just below.
    println("\ncofree_universal(state_system_comonoid(", S, "), labeling, 2) built")

    # Universal property: F.underlying ⨟ cofree_unit == labeling.
    unit_p = cofree_unit(p, 2)
    factored = compose(F.underlying, unit_p)
    @assert factored == labeling
    println("F.underlying ⨟ cofree_unit ≡ labeling ✓ (universal property)")

    # ---- Bicomodules ----
    cb = state_system_comonoid(FinPolySet([:a, :b]))
    Br = regular_bicomodule(cb)
    @assert validate_bicomodule(Br)
    println("\nregular_bicomodule(state_system_comonoid({a,b})): validate ✓")

    println("\n== All Sprint 8 acceptance tests passed. ==")
    true
end

"Show off the pre-Sprint-4 refinements: @poly macro, precedence-aware show, simplify trace, ≈ alias."
function _refinement_demo()
    println("\n== Pre-Sprint-4 refinement demo ==\n")

    p1 = @poly y^3 + 2y + 1
    println("@poly y^3 + 2y + 1 = ", p1)
    @assert is_iso(p1, Polynomial(FinPolySet([1, 2, 3, 4]),
                                   i -> i == 1 ? FinPolySet(1:3) :
                                        i in (2, 3) ? FinPolySet(1:1) :
                                                       FinPolySet(Symbol[])))

    p2 = @poly 2y^2 + 3
    println("@poly 2y^2 + 3      = ", p2)
    @assert cardinality(p2.positions) == Finite(5)

    a, b, c = sympoly(:a), sympoly(:b), sympoly(:c)
    expr = parallel(a + b, c)
    println("\nNo unnecessary parens:")
    println("  parallel(a + b, c) = ", expr)
    @assert occursin("(a + b) ⊗ c", sprint(show, expr.expr))

    expr2 = a + parallel(b, c)
    println("  a + parallel(b, c) = ", expr2)
    @assert !occursin("(b ⊗ c)", sprint(show, expr2.expr))

    e = parallel(a + b, c)
    out, hist = simplify(e; trace=true)
    println("\nsimplify trace for (a + b) ⊗ c:")
    for (k, (rule, intermediate)) in enumerate(hist)
        println("  step $k: ", rule.description, " → ", intermediate)
    end
    println("  final:    ", out)
    @assert length(hist) ≥ 1
    @assert any(r -> occursin("⊗", r[1].description), hist)

    p = @poly y^3 + y
    q = @poly y + y^3
    println("\np = ", p, ",  q = ", q)
    @assert !(p == q)
    @assert p ≈ q
    println("p == q  : ", p == q)
    println("p ≈ q   : ", p ≈ q)

    @assert (a + b) ≈ (b + a)
    @assert parallel(a, sym_y) ≈ a
    println("symbolic: a + b ≈ b + a ✓; a ⊗ y ≈ a ✓")

    println("\n== Refinement demo passed. ==")
    true
end

"Run a small symbolic-layer demo."
function _symbolic_demo()
    println("\n== Symbolic layer demo ==\n")

    p = sympoly(:p)
    f = symlens(:f, dom=p, cod=p)
    id_p = sym_id(p)
    expr1 = compose(f, id_p)
    println("Before simplify: ", expr1)
    simplified = simplify(expr1)
    println("After simplify:  ", simplified)
    @assert simplified == f

    q = sympoly(:q)
    p_plus_zero = p + sym_zero
    println("\np + 0 → ", simplify(p_plus_zero))
    @assert simplify(p_plus_zero) == p

    p_par_y = parallel(p, sym_y)
    println("p ⊗ y → ", simplify(p_par_y))
    @assert simplify(p_par_y) == p

    pq = parallel(p, q)
    @assert sym_equal(pq, parallel(p, q))

    py = parallel(p, sym_y)
    @assert sym_equal(py, p)
    println("\nsym_equal(p ⊗ y, p) = true (via unitor rule)")

    lifted = lift(y)
    println("\nlift(y) = ", lifted)
    @assert lifted == sym_y

    println("\n== Symbolic layer demo passed. ==")
    true
end
