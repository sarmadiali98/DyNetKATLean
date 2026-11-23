import DyNetKATLean

------------------------------------------------------------------------
-- Focused tests for S6B Parts 3A and 3B - semantic soundness
-- (`graphHead_sound`) and semantic completeness (`graphHead_complete`)
-- of graph-native head extraction, plus the combined specification
-- equivalence (`graphHead_spec_iff`),
-- `DyNetKAT.DyNetKAT.GraphHead`.
--
-- Run with:  lake env lean test_graph_head.lean   (from lean/)
--
-- Every fixture applies the ACTUAL soundness theorem
--
--   graphHead_sound G H hhead :
--     ∀ σ τ, Semantics H σ τ → GraphHeadSpec G G.root σ τ
--
-- to a concrete graph fixture (reusing the S6B Part 2 example graphs
-- and their verified extraction results) and derives concrete
-- consequences:
--
--   1. Self-recursive process `X ≜ N;X` - positive spec instance for a
--      concrete packet pair, witnessed by the expected prefix policy,
--      plus a direct exercise of the node-level soundness helper.
--   2. Mutual recursion `X ≜ N;Y`, `Y ≜ M;X` - positive spec instance;
--      both nodes of the cycle contribute, each visited exactly once.
--   3. Unguarded cycle `X ≜ Y`, `Y ≜ X` - the specification is EMPTY
--      (the cyclic references contribute no packet pairs), so
--      soundness is tight: the extracted policy `0 + (0 + 0)` also has
--      empty semantics (`exUnguarded_semantic`).
--   4. Unreachable recursive definition - the specification is empty
--      and the unreachable definition contributes nothing.
--   5. `rcfgPrefix` boundary - the specification of the root is
--      exactly the semantics of the prefix before the boundary;
--      nothing beyond the boundary contributes.
--
-- The Part 3B completeness tests below apply the ACTUAL completeness
-- theorem and the specification equivalence to the same fixtures, plus
-- a supported empty head (Eq. 29) and the unsupported-constructor
-- witness for the necessity of supportedness.
------------------------------------------------------------------------

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.GraphHeadTests

open DyNetKAT.NetKAT

/-- A concrete packet. -/
abbrev σ₀ : CtxPkt := examplePacket

------------------------------------------------------------------------
-- Fixture 1 - the self-recursive process `X ≜ N;X` (N := 1)
------------------------------------------------------------------------

abbrev gSelf : ProcessGraph := exSelfLoopGraph NetKAT.id

theorem gSelf_root : gSelf.root = GProc.ref (varNode "X") := rfl

theorem gSelf_labelX :
    gSelf.label (varNode "X") = .nSeq NetKAT.id (GProc.ref (varNode "X")) := by
  simp [gSelf, exSelfLoopGraph, exSelfLoopLabel, varNode]

theorem gSelf_extracted :
    graphHead gSelf = some (NetKAT.union .drop (NetKAT.union .id .drop)) :=
  exSelfLoop_extracted NetKAT.id

/-- **Test 1 (soundness instance)**: the extracted policy of `X ≜ 1;X`
    is spec-sound. -/
theorem test1_sound (σ τ : CtxPkt) (hsem :
    Semantics (NetKAT.union .drop (NetKAT.union .id .drop)) σ τ) :
    GraphHeadSpec gSelf gSelf.root σ τ :=
  graphHead_sound gSelf _ gSelf_extracted σ τ hsem

/-- The extracted policy contains the diagonal. -/
theorem test1_sem (σ : CtxPkt) :
    Semantics (NetKAT.union .drop (NetKAT.union .id .drop)) σ σ :=
  (union_sem .drop (NetKAT.union .id .drop) σ σ).mpr
    (Or.inr ((union_sem .id .drop σ σ).mpr (Or.inl (id_reflexive σ))))

/-- **Test 1 (concrete consequence)**: soundness yields a concrete
    specification instance for the self-recursive process. -/
theorem test1_concrete : GraphHeadSpec gSelf gSelf.root σ₀ σ₀ :=
  test1_sound σ₀ σ₀ (test1_sem σ₀)

/-- The concrete instance is witnessed by the expected prefix policy `1`
    at the head of the node label `1; ref X`. -/
theorem test1_expected_prefix : HeadPrefixOf gSelf gSelf.root NetKAT.id := by
  rw [gSelf_root]
  exact HeadPrefixOf.ref (varNode "X") NetKAT.id
    (by rw [gSelf_labelX]; exact HeadPrefixOf.here _ _)

/-- The node-level helper in action: the collection of the visited
    node's label `1; ref X` is sound at the root. -/
theorem test1_node_collect :
    headCollect (gSelf.label (varNode "X")) = some (NetKAT.union NetKAT.id .drop) := by
  simp [headCollect, gSelf_labelX]

theorem test1_node_sound (σ τ : CtxPkt)
    (hsem : Semantics (NetKAT.union NetKAT.id .drop) σ τ) :
    GraphHeadSpec gSelf gSelf.root σ τ :=
  headCollect_node_spec_sound gSelf (varNode "X") (HeadPathTo.ref (varNode "X"))
    test1_node_collect σ τ hsem

------------------------------------------------------------------------
-- Fixture 2 - mutually recursive processes `X ≜ N;Y`, `Y ≜ M;X`
-- (N := M := 1)
------------------------------------------------------------------------

abbrev gMut : ProcessGraph := exMutualGraph NetKAT.id NetKAT.id

theorem gMut_root : gMut.root = GProc.ref (varNode "X") := rfl

theorem gMut_labelX :
    gMut.label (varNode "X") = .nSeq NetKAT.id (GProc.ref (varNode "Y")) := by
  simp [gMut, exMutualGraph, exMutualLabel, varNode]

theorem gMut_labelY :
    gMut.label (varNode "Y") = .nSeq NetKAT.id (GProc.ref (varNode "X")) := by
  simp [gMut, exMutualGraph, exMutualLabel, varNode]

theorem gMut_extracted :
    graphHead gMut =
      some (NetKAT.union (NetKAT.union .drop (NetKAT.union .id .drop))
        (NetKAT.union .id .drop)) :=
  exMutual_extracted NetKAT.id NetKAT.id

/-- **Test 2 (soundness instance)**: the extracted policy of the guarded
    mutual recursion is spec-sound. -/
theorem test2_sound (σ τ : CtxPkt) (hsem :
    Semantics (NetKAT.union (NetKAT.union .drop (NetKAT.union .id .drop))
      (NetKAT.union .id .drop)) σ τ) :
    GraphHeadSpec gMut gMut.root σ τ :=
  graphHead_sound gMut _ gMut_extracted σ τ hsem

/-- The extracted policy contains the diagonal. -/
theorem test2_sem (σ : CtxPkt) :
    Semantics (NetKAT.union (NetKAT.union .drop (NetKAT.union .id .drop))
      (NetKAT.union .id .drop)) σ σ :=
  (union_sem _ _ σ σ).mpr (Or.inr ((union_sem _ _ σ σ).mpr (Or.inl (id_reflexive σ))))

/-- **Test 2 (concrete consequence)**: soundness yields a concrete
    specification instance for the mutually recursive processes. -/
theorem test2_concrete : GraphHeadSpec gMut gMut.root σ₀ σ₀ :=
  test2_sound σ₀ σ₀ (test2_sem σ₀)

/-- The concrete instance is witnessed by the expected prefix policy `1`
    at the head of node `X`'s label `1; ref Y`. -/
theorem test2_expected_prefixX : HeadPrefixOf gMut gMut.root NetKAT.id := by
  rw [gMut_root]
  exact HeadPrefixOf.ref (varNode "X") NetKAT.id
    (by rw [gMut_labelX]; exact HeadPrefixOf.here _ _)

/-- ... and by the same prefix policy at the head of node `Y`'s label
    `1; ref X`: both nodes of the cycle contribute, each visited exactly
    once by the worklist. -/
theorem test2_expected_prefixY : HeadPrefixOf gMut gMut.root NetKAT.id := by
  rw [gMut_root]
  refine HeadPrefixOf.ref (varNode "X") NetKAT.id ?_
  rw [gMut_labelX]
  refine HeadPrefixOf.nSeq _ _ _ ?_
  refine HeadPrefixOf.ref (varNode "Y") NetKAT.id ?_
  rw [gMut_labelY]
  exact HeadPrefixOf.here _ _

------------------------------------------------------------------------
-- Fixture 3 - the unguarded cycle `X ≜ Y`, `Y ≜ X`
------------------------------------------------------------------------

abbrev gUng : ProcessGraph := exUnguardedGraph

theorem gUng_root : gUng.root = GProc.ref (varNode "X") := rfl

theorem gUng_labelX : gUng.label (varNode "X") = GProc.ref (varNode "Y") := by
  simp [gUng, exUnguardedGraph, exUnguardedLabel, varNode]

theorem gUng_labelY : gUng.label (varNode "Y") = GProc.ref (varNode "X") := by
  simp [gUng, exUnguardedGraph, exUnguardedLabel, varNode]

theorem gUng_extracted :
    graphHead gUng = some (NetKAT.union (NetKAT.union .drop .drop) .drop) :=
  exUnguarded_extracted

/-- **Test 3 (soundness instance)**: the extracted policy of the
    unguarded cycle is spec-sound. -/
theorem test3_sound (σ τ : CtxPkt) (hsem :
    Semantics (NetKAT.union (NetKAT.union .drop .drop) .drop) σ τ) :
    GraphHeadSpec gUng gUng.root σ τ :=
  graphHead_sound gUng _ gUng_extracted σ τ hsem

/-- The specification of the unguarded cycle is EMPTY: a `GraphHeadSpec`
    derivation for a pure reference cycle would have to descend through
    `ref_of` forever, and the least-fixpoint relation admits no such
    cyclic derivation.  The invariant `gp ∉ {ref X, ref Y}` is preserved
    backwards along every constructor, so no derivation ends at a
    reference.  Soundness is therefore TIGHT here: the extracted policy
    `0 + (0 + 0)` also has empty semantics (`exUnguarded_semantic`), so
    the cycle fabricates no contributions. -/
theorem test3_spec_empty (σ τ : CtxPkt) :
    ¬ GraphHeadSpec gUng gUng.root σ τ := by
  have hinv : ∀ gp σ' τ', GraphHeadSpec gUng gp σ' τ' →
      gp ≠ GProc.ref (varNode "X") ∧ gp ≠ GProc.ref (varNode "Y") := by
    intro gp σ' τ' h
    induction h with
    | nSeq_of_sem _ _ _ _ _ =>
        exact ⟨fun hEq => absurd hEq (by simp), fun hEq => absurd hEq (by simp)⟩
    | nSeq_of_tail _ _ _ _ _ _ =>
        exact ⟨fun hEq => absurd hEq (by simp), fun hEq => absurd hEq (by simp)⟩
    | choice_left _ _ _ _ _ _ =>
        exact ⟨fun hEq => absurd hEq (by simp), fun hEq => absurd hEq (by simp)⟩
    | choice_right _ _ _ _ _ _ =>
        exact ⟨fun hEq => absurd hEq (by simp), fun hEq => absurd hEq (by simp)⟩
    | ref_of i _ _ _ ih =>
        by_cases hiX : i = varNode "X"
        · subst hiX
          rw [gUng_labelX] at ih
          exact absurd rfl ih.2
        · by_cases hiY : i = varNode "Y"
          · subst hiY
            rw [gUng_labelY] at ih
            exact absurd rfl ih.1
          · refine ⟨?_, ?_⟩
            · intro hEq
              injection hEq with h'
              exact hiX h'
            · intro hEq
              injection hEq with h'
              exact hiY h'
  intro h
  exact (hinv _ _ _ h).1 gUng_root

------------------------------------------------------------------------
-- Fixture 4 - an unreachable recursive definition
-- (`X ≜ ⊥` reachable, `Z ≜ P;Z` unreachable)
------------------------------------------------------------------------

abbrev gUnreach : ProcessGraph := exUnreachableGraph NetKAT.id

theorem gUnreach_root : gUnreach.root = GProc.ref (varNode "X") := rfl

theorem gUnreach_labelX : gUnreach.label (varNode "X") = GProc.deadlock := by
  simp [gUnreach, exUnreachableGraph, exUnreachableLabel, varNode]

theorem gUnreach_extracted :
    graphHead gUnreach = some (NetKAT.union .drop .drop) :=
  exUnreachable_extracted NetKAT.id

/-- **Test 4 (soundness instance)**: the extracted policy of the graph
    with an unreachable recursive definition is spec-sound. -/
theorem test4_sound (σ τ : CtxPkt) (hsem :
    Semantics (NetKAT.union .drop .drop) σ τ) :
    GraphHeadSpec gUnreach gUnreach.root σ τ :=
  graphHead_sound gUnreach _ gUnreach_extracted σ τ hsem

/-- The specification of the root is empty: the root references node `X`
    whose label is `⊥`, and `⊥` contributes nothing (Eq. 29).  The
    unreachable recursive definition at node `Z` contributes nothing
    either, so soundness is tight: the extracted policy `0 + 0` also has
    empty semantics (`exUnreachable_semantic`). -/
theorem test4_spec_empty (σ τ : CtxPkt) :
    ¬ GraphHeadSpec gUnreach gUnreach.root σ τ := by
  rw [gUnreach_root, graphHeadSpec_ref_iff, gUnreach_labelX]
  exact graphHeadSpec_deadlock_false gUnreach σ τ

------------------------------------------------------------------------
-- Fixture 5 - an `rcfgPrefix` boundary
-- (`root = 1; rcfg_{ctrl,1}; ref X`, node `X` unsupported)
------------------------------------------------------------------------

abbrev gRcfg : ProcessGraph := exRcfgGraph "ctrl" NetKAT.id

theorem gRcfg_root : gRcfg.root =
    .nSeq NetKAT.id (.rcfgPrefix "ctrl" NetKAT.id (GProc.ref (varNode "X"))) := rfl

theorem gRcfg_extracted : graphHead gRcfg = some (NetKAT.union NetKAT.id .drop) :=
  exRcfg_extracted "ctrl" NetKAT.id

/-- **Test 5 (soundness instance)**: the extracted policy of the
    reconfiguration-boundary graph is spec-sound. -/
theorem test5_sound (σ τ : CtxPkt) (hsem :
    Semantics (NetKAT.union NetKAT.id .drop) σ τ) :
    GraphHeadSpec gRcfg gRcfg.root σ τ :=
  graphHead_sound gRcfg _ gRcfg_extracted σ τ hsem

/-- The extracted policy contains the diagonal. -/
theorem test5_sem (σ : CtxPkt) :
    Semantics (NetKAT.union NetKAT.id .drop) σ σ :=
  (union_sem _ _ σ σ).mpr (Or.inl (id_reflexive σ))

/-- **Test 5 (concrete consequence)**: soundness yields a concrete
    specification instance for the reconfiguration-boundary graph. -/
theorem test5_concrete : GraphHeadSpec gRcfg gRcfg.root σ₀ σ₀ :=
  test5_sound σ₀ σ₀ (test5_sem σ₀)

/-- The boundary contributes nothing: the specification of the root is
    EXACTLY the semantics of the prefix `1` before the `rcfgPrefix`
    (Eq. 32 gives the empty relation at the boundary). -/
theorem test5_spec_iff (σ τ : CtxPkt) :
    GraphHeadSpec gRcfg gRcfg.root σ τ ↔ σ = τ := by
  rw [gRcfg_root, graphHeadSpec_nSeq_iff]
  constructor
  · rintro (hsem | hspec)
    · exact (id_diag σ τ).mp hsem
    · exact absurd hspec
        (graphHeadSpec_rcfgPrefix_false gRcfg "ctrl" NetKAT.id
          (GProc.ref (varNode "X")) σ τ)
  · intro hEq
    exact Or.inl ((id_diag σ τ).mpr hEq)

------------------------------------------------------------------------
-- S6B Part 3B - semantic completeness tests
--
-- Every fixture applies the ACTUAL completeness theorem
--
--   graphHead_complete G H hhead :
--     ∀ σ τ, GraphHeadSpec G G.root σ τ → Semantics H σ τ
--
-- and the combined specification-equivalence theorem
--
--   graphHead_spec_iff G hsupported σ τ :
--     GraphHeadSpec G G.root σ τ ↔ ∃ H, graphHead G = some H ∧ Semantics H σ τ
--
-- to the concrete fixtures:
--
--   1. Self-recursive `X ≜ 1;X` - the spec instance built from the
--      expected prefix `1` is matched by the extracted policy's
--      semantics (round trip through the equivalence).
--   2. Mutual recursion `X ≜ 1;Y`, `Y ≜ 1;X` - both cycle nodes'
--      contributions are captured, each visited exactly once.
--   3. Unguarded cycle `X ≜ Y`, `Y ≜ X` - supported empty head: the
--      specification is empty AND the extracted policy's semantics is
--      empty, so the equivalence holds with both sides empty.
--   4. Unreachable recursive definition - outside the head region, so
--      the shape condition never needs it; the equivalence holds with
--      both sides empty.
--   5. `rcfgPrefix` boundary - the spec of the root coincides exactly
--      with the semantics of the extracted policy `1 + 0`.
--   6. Supported empty head at the root itself (`root = ⊥`, Eq. 29) -
--      extraction yields `some 0` (distinct from `none`), the spec is
--      empty, and the equivalence holds.
--   7. Unsupported reachable constructor (`X ≜ (1;⊥) ⊕ x?1;⊥`) - the
--      extraction fails EXPLICITLY (`none`), supportedness fails, yet
--      the specification is nonempty: this is the witness that the
--      supportedness hypothesis of the packaged completeness and of the
--      equivalence is necessary (no completeness is claimed here).
--
-- No `sorry`, no new axioms; the principal completeness theorems are
-- re-checked with `#print axioms` at the bottom.
------------------------------------------------------------------------

/-- The self-recursive fixture is supported: its head-subterm closure is
    the finite set `{ref X, 1; ref X}`, both supported shapes. -/
theorem gSelf_memX : varNode "X" ∈ gSelf.nodes := by
  simp [gSelf, exSelfLoopGraph, varNode]

theorem gSelf_shapeOk (dst : GProc) (h : HeadSub gSelf gSelf.root dst) :
    HeadShapeOk gSelf dst := by
  refine headShapeOk_of_headSub_inv gSelf _ dst h
    (fun b => b = GProc.ref (varNode "X") ∨
      b = .nSeq NetKAT.id (GProc.ref (varNode "X"))) ?_ ?_ ?_ ?_ ?_
  · exact Or.inl gSelf_root
  · rintro b (hEq | hEq)
    · rw [hEq]; exact HeadShapeOk.ref _ gSelf_memX
    · rw [hEq]; exact HeadShapeOk.nSeq _ _
  · rintro b (hEq | hEq) N cont hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq
      injection hbEq with hN hc
      subst hN; subst hc
      exact Or.inl rfl
  · rintro b (hEq | hEq) x y hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
  · rintro b (hEq | hEq) i hbEq
    · rw [hEq] at hbEq
      injection hbEq with hi
      subst hi
      rw [gSelf_labelX]
      exact ⟨gSelf_memX, Or.inr rfl⟩
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq

theorem gSelf_supported : GraphHeadSupported gSelf :=
  ⟨gSelf_shapeOk, fun j hj => headPathTo_nodes_closed gSelf j hj⟩

/-- **Test 1 (completeness instance)**: every spec behavior of
    `X ≜ 1;X` lies in the semantics of the extracted policy. -/
theorem test1_complete (σ τ : CtxPkt)
    (hspec : GraphHeadSpec gSelf gSelf.root σ τ) :
    Semantics (NetKAT.union .drop (NetKAT.union .id .drop)) σ τ :=
  graphHead_complete gSelf _ gSelf_extracted σ τ hspec

/-- **Test 1 (concrete completeness)**: the concrete spec instance built
    in Part 3A from the expected prefix `1` is matched by the extracted
    policy's semantics on the diagonal. -/
theorem test1_complete_concrete :
    Semantics (NetKAT.union .drop (NetKAT.union .id .drop)) σ₀ σ₀ :=
  test1_complete σ₀ σ₀ test1_concrete

/-- **Test 1 (specification equivalence)**. -/
theorem test1_iff (σ τ : CtxPkt) :
    GraphHeadSpec gSelf gSelf.root σ τ ↔
      ∃ H : NetKAT, graphHead gSelf = some H ∧ Semantics H σ τ :=
  graphHead_spec_iff gSelf gSelf_supported σ τ

/-- **Test 1 (round trip)**: the spec instance survives the equivalence
    into the extracted policy's semantics and back. -/
theorem test1_roundtrip :
    ∃ H : NetKAT, graphHead gSelf = some H ∧ Semantics H σ₀ σ₀ :=
  (test1_iff σ₀ σ₀).mp test1_concrete

/-- The mutually recursive fixture is supported: its head-subterm closure
    is `{ref X, ref Y, 1; ref Y, 1; ref X}` - all supported shapes. -/
theorem gMut_memX : varNode "X" ∈ gMut.nodes := by
  simp [gMut, exMutualGraph, varNode]

theorem gMut_memY : varNode "Y" ∈ gMut.nodes := by
  simp [gMut, exMutualGraph, varNode]

theorem gMut_shapeOk (dst : GProc) (h : HeadSub gMut gMut.root dst) :
    HeadShapeOk gMut dst := by
  refine headShapeOk_of_headSub_inv gMut _ dst h
    (fun b => b = GProc.ref (varNode "X") ∨ b = GProc.ref (varNode "Y") ∨
      b = .nSeq NetKAT.id (GProc.ref (varNode "Y")) ∨
      b = .nSeq NetKAT.id (GProc.ref (varNode "X"))) ?_ ?_ ?_ ?_ ?_
  · exact Or.inl gMut_root
  · rintro b (hEq | hEq | hEq | hEq)
    · rw [hEq]; exact HeadShapeOk.ref _ gMut_memX
    · rw [hEq]; exact HeadShapeOk.ref _ gMut_memY
    · rw [hEq]; exact HeadShapeOk.nSeq _ _
    · rw [hEq]; exact HeadShapeOk.nSeq _ _
  · rintro b (hEq | hEq | hEq | hEq) N cont hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq
      injection hbEq with hN hc
      subst hN; subst hc
      exact Or.inr (Or.inl rfl)
    · rw [hEq] at hbEq
      injection hbEq with hN hc
      subst hN; subst hc
      exact Or.inl rfl
  · rintro b (hEq | hEq | hEq | hEq) x y hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
  · rintro b (hEq | hEq | hEq | hEq) i hbEq
    · rw [hEq] at hbEq
      injection hbEq with hi
      subst hi
      rw [gMut_labelX]
      exact ⟨gMut_memX, Or.inr (Or.inr (Or.inl rfl))⟩
    · rw [hEq] at hbEq
      injection hbEq with hi
      subst hi
      rw [gMut_labelY]
      exact ⟨gMut_memY, Or.inr (Or.inr (Or.inr rfl))⟩
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq

theorem gMut_supported : GraphHeadSupported gMut :=
  ⟨gMut_shapeOk, fun j hj => headPathTo_nodes_closed gMut j hj⟩

/-- **Test 2 (completeness instance)**: every spec behavior of the
    guarded mutual recursion lies in the semantics of the extracted
    policy. -/
theorem test2_complete (σ τ : CtxPkt)
    (hspec : GraphHeadSpec gMut gMut.root σ τ) :
    Semantics (NetKAT.union (NetKAT.union .drop (NetKAT.union .id .drop))
      (NetKAT.union .id .drop)) σ τ :=
  graphHead_complete gMut _ gMut_extracted σ τ hspec

/-- **Test 2 (both cycle nodes contribute)**: the spec instance built
    from node `Y`'s prefix witness `1` (reached through `X ≜ 1;Y` and
    `Y ≜ 1;X`) is matched by the extracted policy's semantics - the
    completeness direction through the two-node cycle. -/
theorem test2_completeY (σ : CtxPkt) :
    Semantics (NetKAT.union (NetKAT.union .drop (NetKAT.union .id .drop))
      (NetKAT.union .id .drop)) σ σ := by
  refine test2_complete σ σ ?_
  exact (graphHeadSpec_iff_prefix gMut gMut.root σ σ).mpr
    ⟨NetKAT.id, test2_expected_prefixY, id_reflexive σ⟩

/-- **Test 2 (specification equivalence and round trip)**. -/
theorem test2_iff (σ τ : CtxPkt) :
    GraphHeadSpec gMut gMut.root σ τ ↔
      ∃ H : NetKAT, graphHead gMut = some H ∧ Semantics H σ τ :=
  graphHead_spec_iff gMut gMut_supported σ τ

theorem test2_roundtrip :
    ∃ H : NetKAT, graphHead gMut = some H ∧ Semantics H σ₀ σ₀ :=
  (test2_iff σ₀ σ₀).mp test2_concrete

/-- The unguarded cycle is supported: its head-subterm closure is
    `{ref X, ref Y}` - both references point at live nodes. -/
theorem gUng_memX : varNode "X" ∈ gUng.nodes := by
  simp [gUng, exUnguardedGraph, varNode]

theorem gUng_memY : varNode "Y" ∈ gUng.nodes := by
  simp [gUng, exUnguardedGraph, varNode]

theorem gUng_shapeOk (dst : GProc) (h : HeadSub gUng gUng.root dst) :
    HeadShapeOk gUng dst := by
  refine headShapeOk_of_headSub_inv gUng _ dst h
    (fun b => b = GProc.ref (varNode "X") ∨ b = GProc.ref (varNode "Y"))
    ?_ ?_ ?_ ?_ ?_
  · exact Or.inl gUng_root
  · rintro b (hEq | hEq)
    · rw [hEq]; exact HeadShapeOk.ref _ gUng_memX
    · rw [hEq]; exact HeadShapeOk.ref _ gUng_memY
  · rintro b (hEq | hEq) N cont hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
  · rintro b (hEq | hEq) x y hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
  · rintro b (hEq | hEq) i hbEq
    · rw [hEq] at hbEq
      injection hbEq with hi
      subst hi
      rw [gUng_labelX]
      exact ⟨gUng_memX, Or.inr rfl⟩
    · rw [hEq] at hbEq
      injection hbEq with hi
      subst hi
      rw [gUng_labelY]
      exact ⟨gUng_memY, Or.inl rfl⟩

theorem gUng_supported : GraphHeadSupported gUng :=
  ⟨gUng_shapeOk, fun j hj => headPathTo_nodes_closed gUng j hj⟩

/-- **Test 3 (completeness instance)**: the completeness theorem applies
    to the unguarded cycle; the spec is empty (test3_spec_empty), so the
    hypothesis is never satisfiable - completeness adds nothing
    spurious. -/
theorem test3_complete (σ τ : CtxPkt)
    (hspec : GraphHeadSpec gUng gUng.root σ τ) :
    Semantics (NetKAT.union (NetKAT.union .drop .drop) .drop) σ τ :=
  graphHead_complete gUng _ gUng_extracted σ τ hspec

/-- **Test 3 (specification equivalence)**. -/
theorem test3_iff (σ τ : CtxPkt) :
    GraphHeadSpec gUng gUng.root σ τ ↔
      ∃ H : NetKAT, graphHead gUng = some H ∧ Semantics H σ τ :=
  graphHead_spec_iff gUng gUng_supported σ τ

/-- **Test 3 (both sides empty)**: the extracted policy `0 + (0 + 0)` has
    empty semantics, so the right side of the equivalence is empty as
    well - the supported empty-head result is exact on both sides. -/
theorem test3_rhs_empty (σ τ : CtxPkt) :
    ¬ (∃ H : NetKAT, graphHead gUng = some H ∧ Semantics H σ τ) := by
  rintro ⟨H, hH, hsem⟩
  rw [gUng_extracted] at hH
  have hH' : NetKAT.union (NetKAT.union .drop .drop) .drop = H :=
    Option.some.inj hH
  subst hH'
  exact exUnguarded_semantic σ τ hsem

theorem test3_both_empty (σ τ : CtxPkt) :
    ¬ GraphHeadSpec gUng gUng.root σ τ ∧
      ¬ (∃ H : NetKAT, graphHead gUng = some H ∧ Semantics H σ τ) :=
  ⟨test3_spec_empty σ τ, test3_rhs_empty σ τ⟩

/-- The unreachable-definition fixture is supported: its head-subterm
    closure is `{ref X, ⊥}` - the unreachable node `Z` is never in the
    head region, so the shape condition never needs its label. -/
theorem gUnreach_memX : varNode "X" ∈ gUnreach.nodes := by
  simp [gUnreach, exUnreachableGraph, varNode]

theorem gUnreach_shapeOk (dst : GProc) (h : HeadSub gUnreach gUnreach.root dst) :
    HeadShapeOk gUnreach dst := by
  refine headShapeOk_of_headSub_inv gUnreach _ dst h
    (fun b => b = GProc.ref (varNode "X") ∨ b = GProc.deadlock) ?_ ?_ ?_ ?_ ?_
  · exact Or.inl gUnreach_root
  · rintro b (hEq | hEq)
    · rw [hEq]; exact HeadShapeOk.ref _ gUnreach_memX
    · rw [hEq]; exact HeadShapeOk.deadlock
  · rintro b (hEq | hEq) N cont hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
  · rintro b (hEq | hEq) x y hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
  · rintro b (hEq | hEq) i hbEq
    · rw [hEq] at hbEq
      injection hbEq with hi
      subst hi
      rw [gUnreach_labelX]
      exact ⟨gUnreach_memX, Or.inr rfl⟩
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq

theorem gUnreach_supported : GraphHeadSupported gUnreach :=
  ⟨gUnreach_shapeOk, fun j hj => headPathTo_nodes_closed gUnreach j hj⟩

/-- Every head-subterm of the unreachable-definition fixture's root is
    either the root reference itself or the root label `⊥`: the
    unreachable recursive definition `Z ≜ P;Z` lies OUTSIDE the head
    region. -/
theorem gUnreach_headSub_cases : ∀ (a dst : GProc), HeadSub gUnreach a dst →
    a = GProc.ref (varNode "X") →
    dst = GProc.ref (varNode "X") ∨ dst = GProc.deadlock := by
  intro a dst h
  induction h with
  | refl gp => intro hEq; exact Or.inl hEq
  | nSeq N cont sub _ _ih => intro hEq; exact GProc.noConfusion hEq
  | choice_left a b sub _ _ih => intro hEq; exact GProc.noConfusion hEq
  | choice_right a b sub _ _ih => intro hEq; exact GProc.noConfusion hEq
  | ref i sub h' _ih =>
      intro hEq
      injection hEq with hi
      subst hi
      rw [gUnreach_labelX] at h'
      cases h' with
      | refl _gp => exact Or.inr rfl

/-- **Test 4 (the unreachable definition is outside the head region)**:
    `Z ≜ P;Z` is not a head-subterm of the root, so completeness and the
    shape condition are unaffected by it. -/
theorem test4_Z_outside (P : NetKAT) :
    ¬ HeadSub gUnreach gUnreach.root (.nSeq P (GProc.ref (varNode "Z"))) := by
  intro h
  rcases gUnreach_headSub_cases _ _ h gUnreach_root with hEq | hEq
  · exact GProc.noConfusion hEq
  · exact GProc.noConfusion hEq

/-- **Test 4 (specification equivalence)**: the equivalence holds; the
    unreachable definition contributes nothing to either side. -/
theorem test4_iff (σ τ : CtxPkt) :
    GraphHeadSpec gUnreach gUnreach.root σ τ ↔
      ∃ H : NetKAT, graphHead gUnreach = some H ∧ Semantics H σ τ :=
  graphHead_spec_iff gUnreach gUnreach_supported σ τ

theorem test4_rhs_empty (σ τ : CtxPkt) :
    ¬ (∃ H : NetKAT, graphHead gUnreach = some H ∧ Semantics H σ τ) := by
  rintro ⟨H, hH, hsem⟩
  rw [gUnreach_extracted] at hH
  have hH' : NetKAT.union .drop .drop = H := Option.some.inj hH
  subst hH'
  exact exUnreachable_semantic NetKAT.id σ τ hsem

theorem test4_both_empty (σ τ : CtxPkt) :
    ¬ GraphHeadSpec gUnreach gUnreach.root σ τ ∧
      ¬ (∃ H : NetKAT, graphHead gUnreach = some H ∧ Semantics H σ τ) :=
  ⟨test4_spec_empty σ τ, test4_rhs_empty σ τ⟩

/-- The reconfiguration-boundary fixture is supported: its head-subterm
    closure is `{1; rcfg…, rcfg…}` - the reference behind the boundary
    and its unsupported label are OUTSIDE the head region. -/
theorem gRcfg_shapeOk (dst : GProc) (h : HeadSub gRcfg gRcfg.root dst) :
    HeadShapeOk gRcfg dst := by
  refine headShapeOk_of_headSub_inv gRcfg _ dst h
    (fun b => b = gRcfg.root ∨
      b = .rcfgPrefix "ctrl" NetKAT.id (GProc.ref (varNode "X"))) ?_ ?_ ?_ ?_ ?_
  · exact Or.inl rfl
  · rintro b (hEq | hEq)
    · rw [hEq]; exact HeadShapeOk.nSeq _ _
    · rw [hEq]; exact HeadShapeOk.rcfgPrefix _ _ _
  · rintro b (hEq | hEq) N cont hbEq
    · rw [hEq] at hbEq
      injection hbEq with hN hc
      subst hN; subst hc
      exact Or.inr rfl
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
  · rintro b (hEq | hEq) x y hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
  · rintro b (hEq | hEq) i hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq
    · rw [hEq] at hbEq; exact GProc.noConfusion hbEq

theorem gRcfg_supported : GraphHeadSupported gRcfg :=
  ⟨gRcfg_shapeOk, fun j hj => headPathTo_nodes_closed gRcfg j hj⟩

/-- **Test 5 (completeness instance)**: every spec behavior of the
    reconfiguration-boundary graph lies in the semantics of the
    extracted policy `1 + 0`. -/
theorem test5_complete (σ τ : CtxPkt)
    (hspec : GraphHeadSpec gRcfg gRcfg.root σ τ) :
    Semantics (NetKAT.union NetKAT.id .drop) σ τ :=
  graphHead_complete gRcfg _ gRcfg_extracted σ τ hspec

/-- **Test 5 (specification equivalence and round trip)**. -/
theorem test5_iff (σ τ : CtxPkt) :
    GraphHeadSpec gRcfg gRcfg.root σ τ ↔
      ∃ H : NetKAT, graphHead gRcfg = some H ∧ Semantics H σ τ :=
  graphHead_spec_iff gRcfg gRcfg_supported σ τ

theorem test5_roundtrip :
    ∃ H : NetKAT, graphHead gRcfg = some H ∧ Semantics H σ₀ σ₀ :=
  (test5_iff σ₀ σ₀).mp test5_concrete

/-- **Test 5 (boundary tightness)**: the spec of the root coincides
    exactly with the semantics of the extracted policy - completeness
    adds nothing beyond the reconfiguration boundary. -/
theorem test5_boundary_tight (σ τ : CtxPkt) :
    GraphHeadSpec gRcfg gRcfg.root σ τ ↔
      Semantics (NetKAT.union NetKAT.id .drop) σ τ := by
  rw [test5_spec_iff]
  exact ((exRcfg_semantic NetKAT.id σ τ).trans (id_diag σ τ)).symm

------------------------------------------------------------------------
-- Test 6 - supported empty head at the root itself (`root = ⊥`, Eq. 29)
------------------------------------------------------------------------

/-- The deadlock-rooted graph: a well-formed graph whose root contributes
    no references and whose head is empty by Eq. (29). -/
def exDeadlockGraph : ProcessGraph where
  nodes := ∅
  root := .deadlock
  label := fun _ => .deadlock
  root_closed := by
    intro i hi
    simp [gprocRefs] at hi
  closed := by
    intro i _hi k hk
    exact absurd hk (Finset.not_mem_empty k)

/-- The extraction yields `some 0` - a valid empty head, distinct from
    the failure `none`. -/
theorem exDeadlock_extracted : graphHead exDeadlockGraph = some .drop := by
  simp [graphHead, graphHeadUnion, unionOverList, unionStep, headCollect,
    headRun, headRefsList, exDeadlockGraph]

theorem exDeadlock_supported : GraphHeadSupported exDeadlockGraph := by
  refine ⟨?_, fun j hj => headPathTo_nodes_closed exDeadlockGraph j hj⟩
  intro dst h
  refine headShapeOk_of_headSub_inv exDeadlockGraph _ dst h
    (fun b => b = GProc.deadlock) rfl ?_ ?_ ?_ ?_
  · rintro b hEq; rw [hEq]; exact HeadShapeOk.deadlock
  · rintro b hEq N cont hbEq; rw [hEq] at hbEq; exact GProc.noConfusion hbEq
  · rintro b hEq x y hbEq; rw [hEq] at hbEq; exact GProc.noConfusion hbEq
  · rintro b hEq i hbEq; rw [hEq] at hbEq; exact GProc.noConfusion hbEq

/-- **Test 6 (completeness instance)**: the completeness theorem applies
    to the supported empty head; the spec is empty (Eq. 29), so the
    hypothesis is never satisfiable. -/
theorem test6_complete (σ τ : CtxPkt)
    (hspec : GraphHeadSpec exDeadlockGraph exDeadlockGraph.root σ τ) :
    Semantics .drop σ τ :=
  graphHead_complete exDeadlockGraph .drop exDeadlock_extracted σ τ hspec

/-- **Test 6 (specification equivalence)**. -/
theorem test6_iff (σ τ : CtxPkt) :
    GraphHeadSpec exDeadlockGraph exDeadlockGraph.root σ τ ↔
      ∃ H : NetKAT, graphHead exDeadlockGraph = some H ∧ Semantics H σ τ :=
  graphHead_spec_iff exDeadlockGraph exDeadlock_supported σ τ

/-- **Test 6 (both sides empty)**: `some 0` has empty semantics, so the
    right side of the equivalence is empty as well - the extraction
    result is distinguished from `none` yet contributes nothing. -/
theorem test6_rhs_empty (σ τ : CtxPkt) :
    ¬ (∃ H : NetKAT, graphHead exDeadlockGraph = some H ∧ Semantics H σ τ) := by
  rintro ⟨H, hH, hsem⟩
  rw [exDeadlock_extracted] at hH
  have hH' : NetKAT.drop = H := Option.some.inj hH
  subst hH'
  exact sem_drop_false σ τ hsem

theorem test6_both_empty (σ τ : CtxPkt) :
    ¬ GraphHeadSpec exDeadlockGraph exDeadlockGraph.root σ τ ∧
      ¬ (∃ H : NetKAT, graphHead exDeadlockGraph = some H ∧ Semantics H σ τ) :=
  ⟨graphHeadSpec_deadlock_false exDeadlockGraph σ τ, test6_rhs_empty σ τ⟩

------------------------------------------------------------------------
-- Test 7 - unsupported reachable constructor: explicit failure, and the
-- necessity of the supportedness hypothesis
------------------------------------------------------------------------

/-- The label of the unsupported-constructor fixture: node `X` is defined
    as `(1;⊥) ⊕ (x?1;⊥)` - the `recv` branch is unsupported. -/
def exUnsupportedLabel (x : Channel) (i : NodeId) : GProc :=
  match i with
  | Sum.inl "X" => .choice (.nSeq .id .deadlock) (.recv x .id .deadlock)
  | _ => .deadlock

/-- Example graph with an unsupported constructor in the head region. -/
def exUnsupportedGraph (x : Channel) : ProcessGraph where
  nodes := {varNode "X"}
  root := .ref (varNode "X")
  label := exUnsupportedLabel x
  root_closed := by
    intro i hi
    simpa [gprocRefs] using hi
  closed := by
    intro i hi
    have hiX : i = varNode "X" := by simpa using hi
    subst hiX
    intro k hk
    simp [exUnsupportedLabel, gprocRefs, varNode] at hk

theorem exUnsupported_labelX (x : Channel) :
    (exUnsupportedGraph x).label (varNode "X") =
      .choice (.nSeq NetKAT.id .deadlock) (.recv x NetKAT.id .deadlock) := by
  simp [exUnsupportedGraph, exUnsupportedLabel, varNode]

/-- **Test 7 (explicit failure)**: the extraction fails EXPLICITLY -
    `none`, never a silent conversion to `0`. -/
theorem exUnsupported_none (x : Channel) :
    graphHead (exUnsupportedGraph x) = none := by
  simp [graphHead, graphHeadUnion, unionOverList, unionStep, headCollect,
    headRun, headRefsList, exUnsupportedGraph, exUnsupportedLabel, varNode]

/-- **Test 7 (the specification is nonetheless nonempty)**: the supported
    branch `1;⊥` contributes the diagonal, so `GraphHeadSpec` holds -
    completeness CANNOT be packaged without supportedness. -/
theorem exUnsupported_spec (x : Channel) (σ : CtxPkt) :
    GraphHeadSpec (exUnsupportedGraph x) (exUnsupportedGraph x).root σ σ := by
  have hroot : (exUnsupportedGraph x).root = GProc.ref (varNode "X") := rfl
  rw [hroot, graphHeadSpec_ref_iff, exUnsupported_labelX,
    graphHeadSpec_choice_iff]
  refine Or.inl ?_
  rw [graphHeadSpec_nSeq_iff]
  exact Or.inl (id_reflexive σ)

/-- **Test 7 (supportedness fails)**: the unsupported `recv` branch is a
    head-subterm of the root, so the shape condition of
    `GraphHeadSupported` fails. -/
theorem exUnsupported_not_supported (x : Channel) :
    ¬ GraphHeadSupported (exUnsupportedGraph x) := by
  rintro ⟨hshape, _⟩
  refine headUnsupported_not_shapeOk
    (G := exUnsupportedGraph x) (HeadUnsupported.recv x NetKAT.id .deadlock) ?_
  apply hshape
  exact HeadSub.ref (varNode "X") _
    (HeadSub.choice_right _ _ _ (HeadSub.refl _))

/-- **Test 7 (no extraction result exists)**: with `graphHead = none`
    there is no `H` at all, so the packaged completeness statement
    `∃ H, graphHead G = some H ∧ Semantics H σ τ` is FALSE while the
    specification is TRUE - the supportedness hypothesis is necessary. -/
theorem exUnsupported_no_extraction (x : Channel) (σ τ : CtxPkt) :
    ¬ (∃ H : NetKAT, graphHead (exUnsupportedGraph x) = some H ∧
        Semantics H σ τ) := by
  rintro ⟨H, hH, _⟩
  rw [exUnsupported_none x] at hH
  exact Option.noConfusion hH

------------------------------------------------------------------------
-- Axiom footprint of the principal soundness and completeness theorems
-- (expect only the standard Mathlib axioms, no `sorryAx`).
------------------------------------------------------------------------

#print axioms graphHead_sound
#print axioms graphHeadUnion_sound
#print axioms headCollect_headSub_spec_sound
#print axioms headCollect_root_spec_sound
#print axioms headCollect_node_spec_sound
#print axioms graphHead_sound_of_supported
#print axioms graphHead_complete
#print axioms graphHeadUnion_complete
#print axioms headCollect_prefix_complete
#print axioms headSub_collection_point
#print axioms graphHead_complete_of_supported
#print axioms graphHead_complete_of_shapeOk_root
#print axioms graphHead_spec_iff
#print axioms graphHead_spec_iff_of_shapeOk_root
#print axioms headShapeOk_of_headSub_inv

end DyNetKAT.DyNetKAT.GraphHeadTests
