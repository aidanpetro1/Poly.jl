# ============================================================
# v0.4 #3: free_labeled_transition_comonoid (post-shim removal)
# ============================================================
#
# `free_category_comonoid` was deprecated in v0.3.1 and removed in v0.4.
# This file mirrors the test coverage from `test_extensions_v2_free_category.jl`
# (now retired) but exercises the canonical `free_labeled_transition_comonoid`
# with the `(src, label, tgt)` edge shape and `max_path_length` keyword.
#
# Coverage:
#
#   1. Acyclic line graph A → B → C: built without warning, validates.
#   2. Acyclic graph with parallel edges (auto-labeled): both parallel
#      edges become distinct morphisms.
#   3. Mixed labeled and unlabeled edges in same call.
#   4. Cyclic graph without `max_path_length`: errors.
#   5. Cyclic graph with `max_path_length`: warns, returns truncation, and
#      validate_comonoid fails (sentinel composites violate category laws).
#   6. Bad input: edge endpoint not in positions errors.
#   7. Bad input: duplicate explicit edge label from same source errors.
#   8. Adversarial cases (mixed types, diamond, multi-cycle, etc.).

@testset "v0.4 #3: free_labeled_transition_comonoid" begin

    @testset "acyclic line graph: 3 positions, 2 edges" begin
        # A → B → C. 3 ids + 2 length-1 + 1 length-2 = 6.
        c = free_labeled_transition_comonoid([:A, :B, :C], [(:A, :B), (:B, :C)])
        @test c isa Comonoid
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.objects.elements) == 3
        @test length(cat.morphisms.elements) == 6
    end

    @testset "acyclic with parallel edges (auto-labeled)" begin
        c = free_labeled_transition_comonoid([:A, :B], [(:A, :B), (:A, :B)])
        @test validate_comonoid(c)
        cat = to_category(c)
        # 2 ids + 2 distinct length-1 paths = 4.
        @test length(cat.morphisms.elements) == 4
    end

    @testset "mixed labeled / unlabeled edges" begin
        # Edge shape: (src, label, tgt) for labeled; (src, tgt) for auto-labeled.
        c = free_labeled_transition_comonoid([:A, :B, :C],
                                             [(:A, :forward, :B),
                                              (:B, :C),                # auto-labeled
                                              (:A, :shortcut, :C)])
        @test validate_comonoid(c)
        cat = to_category(c)
        # 3 ids + 3 length-1 + 1 length-2 (forward then auto) = 7.
        @test length(cat.morphisms.elements) == 7
    end

    @testset "single position, no edges: trivial category" begin
        c = free_labeled_transition_comonoid([:lone], Tuple[])
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.objects.elements) == 1
        @test length(cat.morphisms.elements) == 1
    end

    @testset "cyclic without max_path_length errors" begin
        @test_throws ErrorException free_labeled_transition_comonoid(
            [:A, :B], [(:A, :B), (:B, :A)])
    end

    @testset "cyclic with max_path_length: warns, returns truncation, validation fails" begin
        c = @test_logs (:warn, r"cycles") free_labeled_transition_comonoid(
            [:A, :B], [(:A, :B), (:B, :A)]; max_path_length=2)
        @test c isa Comonoid
        @test !validate_comonoid(c)
        cat = to_category(c)
        # 2 ids + 2 length-1 + 2 length-2 = 6.
        @test length(cat.morphisms.elements) == 6
    end

    @testset "self-loop with max_path_length=3" begin
        c = @test_logs (:warn, r"cycles") free_labeled_transition_comonoid(
            [:A], [(:A, :A)]; max_path_length=3)
        cat = to_category(c)
        # identity + length 1, 2, 3 = 4.
        @test length(cat.morphisms.elements) == 4
    end

    @testset "edge endpoint not in positions errors" begin
        @test_throws ErrorException free_labeled_transition_comonoid(
            [:A], [(:A, :NotPresent)])
    end

    @testset "duplicate explicit edge label from same source errors" begin
        # New edge shape: (src, label, tgt). Duplicate label from same source.
        @test_throws ErrorException free_labeled_transition_comonoid(
            [:A, :B], [(:A, :tag, :B), (:A, :tag, :B)])
    end

    @testset "deduplicates positions" begin
        c = free_labeled_transition_comonoid([:A, :A, :B], [(:A, :B)])
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.objects.elements) == 2
    end

    # ============================================================
    # Adversarial tests (mirror the v2 file)
    # ============================================================

    @testset "adversarial — long acyclic chain validates" begin
        # 10-vertex chain. 10 ids + 9 + 8 + ... + 1 = 10 + 45 = 55.
        verts = [Symbol("v$i") for i in 1:10]
        edges = [(verts[i], verts[i+1]) for i in 1:9]
        c = free_labeled_transition_comonoid(verts, edges)
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.morphisms.elements) == 55
    end

    @testset "adversarial — disconnected components" begin
        c = free_labeled_transition_comonoid([:A, :B, :X, :Y],
                                             [(:A, :B), (:X, :Y)])
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.objects.elements) == 4
        @test length(cat.morphisms.elements) == 6
        for ((f, g), _) in cat.composition
            f_dom_first = cat.dom[f]
            g_dom_first = cat.dom[g]
            same_side = (f_dom_first in (:A, :B) && g_dom_first in (:A, :B)) ||
                        (f_dom_first in (:X, :Y) && g_dom_first in (:X, :Y))
            @test same_side
        end
    end

    @testset "adversarial — mixed types in positions" begin
        c = free_labeled_transition_comonoid(Any[:A, 42, "str"],
                                             Any[(:A, 42), (42, "str")])
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.objects.elements) == 3
    end

    @testset "adversarial — auto-label collides with explicit Int label" begin
        # First edge auto-labeled 1; second edge explicitly labeled 1 from
        # same source. Duplicate-label check should fire.
        @test_throws ErrorException free_labeled_transition_comonoid(
            [:A, :B], [(:A, :B), (:A, 1, :B)])
    end

    @testset "adversarial — auto-labels distinct on different sources" begin
        c = free_labeled_transition_comonoid([:A, :B, :C],
                                             [(:A, :B), (:B, :C)])
        @test validate_comonoid(c)
    end

    @testset "adversarial — max_path_length=0 with cycles gives only identities" begin
        c = @test_logs (:warn, r"cycles") free_labeled_transition_comonoid(
            [:A, :B], [(:A, :B), (:B, :A)]; max_path_length=0)
        cat = to_category(c)
        @test length(cat.morphisms.elements) == 2
        @test validate_comonoid(c)
    end

    @testset "adversarial — multi-cycle graph (two disjoint 2-cycles)" begin
        c = @test_logs (:warn, r"cycles") free_labeled_transition_comonoid(
            [:A, :B, :X, :Y],
            [(:A, :B), (:B, :A), (:X, :Y), (:Y, :X)]; max_path_length=2)
        cat = to_category(c)
        # 4 ids + 4 length-1 + 4 length-2 = 12.
        @test length(cat.morphisms.elements) == 12
    end

    @testset "adversarial — bare-tuple form rejects 1-tuple" begin
        @test_throws ErrorException free_labeled_transition_comonoid([:A], [(:A,)])
    end

    @testset "adversarial — bare-tuple form rejects 4-tuple" begin
        @test_throws ErrorException free_labeled_transition_comonoid(
            [:A, :B], [(:A, :B, :extra1, :extra2)])
    end

    @testset "adversarial — empty edge list (only identities)" begin
        c = free_labeled_transition_comonoid([:A, :B, :C], Tuple[])
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.morphisms.elements) == 3
    end

    @testset "adversarial — diamond graph (DAG, multiple paths)" begin
        # A → B, A → C, B → D, C → D. Two paths A → D.
        c = free_labeled_transition_comonoid([:A, :B, :C, :D],
                                             [(:A, :ab, :B), (:A, :ac, :C),
                                              (:B, :bd, :D), (:C, :cd, :D)])
        @test validate_comonoid(c)
        cat = to_category(c)
        # 4 ids + 4 length-1 + 2 length-2 (ab→bd, ac→cd) = 10.
        @test length(cat.morphisms.elements) == 10
    end

    @testset "adversarial — non-symbol labels" begin
        c = free_labeled_transition_comonoid(["start", "mid", "end"],
                                             [("start", "mid"), ("mid", "end")])
        @test validate_comonoid(c)
        cat = to_category(c)
        @test length(cat.objects.elements) == 3
    end

    # ============================================================
    # New v0.4-specific test: free_category_comonoid is gone.
    # ============================================================

    @testset "v0.4: free_category_comonoid no longer defined" begin
        @test !isdefined(@__MODULE__, :free_category_comonoid)
    end

end
