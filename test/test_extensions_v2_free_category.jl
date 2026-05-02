# ============================================================
# Extensions v2, PR #14: free_category_comonoid
# ============================================================
#
# Coverage:
#
#   1. Acyclic line graph A → B → C: built without warning, validates.
#      Has 3 identity morphisms + 2 length-1 paths + 1 length-2 path = 6
#      morphisms.
#   2. Acyclic graph with parallel edges (auto-labeled): both parallel
#      edges become distinct morphisms.
#   3. Mixed labeled and unlabeled edges in same call.
#   4. Cyclic graph without `max_depth`: errors.
#   5. Cyclic graph with `max_depth`: warns, returns a truncation, and
#      validate_comonoid fails (missing compositions exceeding the bound).
#   6. Cyclic graph at `max_depth=2` has the right morphism count.
#   7. Bad input: edge endpoint not in vertices errors.
#   8. Bad input: duplicate explicit edge label from same source errors.

@testset "Extensions v2, PR #14: free_category_comonoid" begin

    @testset "acyclic line graph: 3 vertices, 2 edges" begin
        # A → B → C. Free category has 3 identities, 2 length-1 paths, 1 length-2 path.
        c = free_category_comonoid([:A, :B, :C], [(:A, :B), (:B, :C)])
        @test c isa Comonoid
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.objects.elements) == 3
        @test length(cat.morphisms.elements) == 6
    end

    @testset "acyclic with parallel edges (auto-labeled)" begin
        # Two parallel edges A → B; auto-labeling distinguishes them.
        c = free_category_comonoid([:A, :B], [(:A, :B), (:A, :B)])
        @test validate_comonoid(c)
        cat = to_category(c)
        # 2 identities + 2 distinct length-1 paths = 4.
        @test length(cat.morphisms.elements) == 4
    end

    @testset "mixed labeled / unlabeled edges" begin
        c = free_category_comonoid([:A, :B, :C],
                                   [(:A, :B, :forward),
                                    (:B, :C),                   # auto-labeled
                                    (:A, :C, :shortcut)])
        @test validate_comonoid(c)
        cat = to_category(c)
        # 3 ids + 3 length-1 paths + 1 length-2 (forward then auto) = 7.
        @test length(cat.morphisms.elements) == 7
    end

    @testset "single vertex, no edges: trivial category" begin
        c = free_category_comonoid([:lone], Tuple[])
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.objects.elements) == 1
        @test length(cat.morphisms.elements) == 1   # only the identity
    end

    @testset "cyclic without max_depth errors" begin
        @test_throws ErrorException free_category_comonoid(
            [:A, :B], [(:A, :B), (:B, :A)])
    end

    @testset "cyclic with max_depth: warns, returns truncation, validation fails" begin
        # A ↔ B cycle with max_depth=2. Expect a warning and a Comonoid
        # whose validation fails (missing compositions for paths > 2).
        c = @test_logs (:warn, r"cycles") free_category_comonoid(
            [:A, :B], [(:A, :B), (:B, :A)]; max_depth=2)
        @test c isa Comonoid
        # Truncation isn't a valid free comonoid — composition is partial.
        @test !validate_comonoid(c)
        cat = to_category(c)
        # 2 identities + paths of length 1 (2 of them) + paths of length 2 (2 of them) = 6.
        @test length(cat.morphisms.elements) == 6
    end

    @testset "self-loop with max_depth=3" begin
        c = @test_logs (:warn, r"cycles") free_category_comonoid(
            [:A], [(:A, :A)]; max_depth=3)
        cat = to_category(c)
        # identity + length 1, 2, 3 = 4 morphisms total.
        @test length(cat.morphisms.elements) == 4
    end

    @testset "edge endpoint not in vertices errors" begin
        @test_throws ErrorException free_category_comonoid(
            [:A], [(:A, :NotPresent)])
    end

    @testset "duplicate explicit edge label from same source errors" begin
        @test_throws ErrorException free_category_comonoid(
            [:A, :B], [(:A, :B, :tag), (:A, :B, :tag)])
    end

    @testset "deduplicates vertices" begin
        # Same vertex listed twice; should silently dedupe and treat as one.
        c = free_category_comonoid([:A, :A, :B], [(:A, :B)])
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.objects.elements) == 2
    end

    # ============================================================
    # Adversarial tests
    # ============================================================

    @testset "adversarial — long acyclic chain validates" begin
        # A 10-vertex chain. 10 ids + 9 length-1 + 8 length-2 + ... + 1 length-9 = 10 + 45 = 55.
        verts = [Symbol("v$i") for i in 1:10]
        edges = [(verts[i], verts[i+1]) for i in 1:9]
        c = free_category_comonoid(verts, edges)
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.morphisms.elements) == 55
    end

    @testset "adversarial — disconnected components" begin
        # Two disjoint chains: A → B and X → Y. No paths cross the gap;
        # composition between them should be impossible (cod of any A-side
        # morphism never matches dom of any X-side morphism).
        c = free_category_comonoid([:A, :B, :X, :Y],
                                   [(:A, :B), (:X, :Y)])
        @test validate_comonoid(c)
        cat = to_category(c)
        # 4 ids + 2 length-1 paths = 6 morphisms total.
        @test length(cat.objects.elements) == 4
        @test length(cat.morphisms.elements) == 6
        # Verify no cross-component composition exists.
        for ((f, g), _) in cat.composition
            f_dom_first = cat.dom[f]
            g_dom_first = cat.dom[g]
            # Both endpoints stay on the same side.
            same_side = (f_dom_first in (:A, :B) && g_dom_first in (:A, :B)) ||
                        (f_dom_first in (:X, :Y) && g_dom_first in (:X, :Y))
            @test same_side
        end
    end

    @testset "adversarial — mixed types in vertices" begin
        # Vertices can be any hashable type; mixing should work as long as
        # equality/hashing are consistent.
        c = free_category_comonoid(Any[:A, 42, "str"],
                                   Any[(:A, 42), (42, "str")])
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.objects.elements) == 3
    end

    @testset "adversarial — auto-label collides with explicit Int label" begin
        # First edge auto-labeled 1; second edge explicitly labeled 1 from
        # same source. Duplicate-label check should fire.
        @test_throws ErrorException free_category_comonoid(
            [:A, :B], [(:A, :B), (:A, :B, 1)])
    end

    @testset "adversarial — auto-labels distinct from explicit labels on different sources" begin
        # Edge 1 from :A is auto-labeled 1; edge 2 from :B is auto-labeled 2.
        # Per-source uniqueness only — 1 and 2 don't collide.
        c = free_category_comonoid([:A, :B, :C],
                                   [(:A, :B), (:B, :C)])
        @test validate_comonoid(c)
    end

    @testset "adversarial — max_depth=0 with cycles gives only identities" begin
        # Truncate to length 0: only identity morphisms.
        c = @test_logs (:warn, r"cycles") free_category_comonoid(
            [:A, :B], [(:A, :B), (:B, :A)]; max_depth=0)
        cat = to_category(c)
        # 2 identities, no other paths.
        @test length(cat.morphisms.elements) == 2
        # Without longer paths, composition is just id ∘ id = id at each
        # object. No sentinels needed; this case ought to pass validation.
        # (Identities composed with identities are well-defined.)
        @test validate_comonoid(c)
    end

    @testset "adversarial — multi-cycle graph (two disjoint cycles)" begin
        # Two independent 2-cycles: A↔B and X↔Y. Both contribute to the
        # cycle detector triggering; the truncation hits both equally.
        c = @test_logs (:warn, r"cycles") free_category_comonoid(
            [:A, :B, :X, :Y],
            [(:A, :B), (:B, :A), (:X, :Y), (:Y, :X)]; max_depth=2)
        cat = to_category(c)
        # 4 ids + 4 length-1 paths + 4 length-2 paths = 12 morphisms.
        @test length(cat.morphisms.elements) == 12
    end

    @testset "adversarial — bare-tuple form rejects 1-tuple" begin
        # _normalize_edge only accepts arity 2 or 3; arity 1 should error.
        @test_throws ErrorException free_category_comonoid([:A], [(:A,)])
    end

    @testset "adversarial — bare-tuple form rejects 4-tuple" begin
        # Arity 4 also out of range.
        @test_throws ErrorException free_category_comonoid([:A, :B],
                                                            [(:A, :B, :extra1, :extra2)])
    end

    @testset "adversarial — empty edge list is valid (only identities)" begin
        # No edges = 3 isolated vertices = 3 identities, no other paths.
        c = free_category_comonoid([:A, :B, :C], Tuple[])
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.morphisms.elements) == 3
    end

    @testset "adversarial — diamond graph (DAG, multiple paths between two vertices)" begin
        # A → B, A → C, B → D, C → D. Two paths from A to D.
        c = free_category_comonoid([:A, :B, :C, :D],
                                   [(:A, :B, :ab), (:A, :C, :ac),
                                    (:B, :D, :bd), (:C, :D, :cd)])
        @test validate_comonoid(c)
        cat = to_category(c)
        # 4 ids + 4 length-1 + 2 length-2 (ab→bd, ac→cd) = 10 morphisms.
        @test length(cat.morphisms.elements) == 10
    end

    @testset "adversarial — non-symbol vertex labels" begin
        # Strings and integers mixed in.
        c = free_category_comonoid(["start", "mid", "end"],
                                   [("start", "mid"), ("mid", "end")])
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.objects.elements) == 3
    end

end
