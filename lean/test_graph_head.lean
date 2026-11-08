import DyNetKAT

------------------------------------------------------------------------
-- Focused tests for S6B Part 3A — semantic soundness of graph-native
-- head extraction (`graphHead_sound`, `DyNetKAT.DyNetKAT.GraphHead`).
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
--   1. Self-recursive process `X ≜ N;X` — positive spec instance for a
--      concrete packet pair, witnessed by the expected prefix policy,
--      plus a direct exercise of the node-level soundness helper.
--   2. Mutual recursion `X ≜ N;Y`, `Y ≜ M;X` — positive spec instance;
--      both nodes of the cycle contribute, each visited exactly once.
--   3. Unguarded cycle `X ≜ Y`, `Y ≜ X` — the specification is EMPTY
--      (the cyclic references contribute no packet pairs), so
--      soundness is tight: the extracted policy `0 + (0 + 0)` also has
--      empty semantics (`exUnguarded_semantic`).
--   4. Unreachable recursive definition — the specification is empty
--      and the unreachable definition contributes nothing.
--   5. `rcfgPrefix` boundary — the specification of the root is
--      exactly the semantics of the prefix before the boundary;
--      nothing beyond the boundary contributes.
--
-- No `sorry`, no new axioms; the principal soundness theorem is
-- re-checked with `#print axioms` at the bottom.
------------------------------------------------------------------------

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.GraphHeadTests

open DyNetKAT.NetKAT

/-- A concrete packet. -/
abbrev σ₀ : CtxPkt := examplePacket

------------------------------------------------------------------------
-- Fixture 1 — the self-recursive process `X ≜ N;X` (N := 1)
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
-- Fixture 2 — mutually recursive processes `X ≜ N;Y`, `Y ≜ M;X`
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
-- Fixture 3 — the unguarded cycle `X ≜ Y`, `Y ≜ X`
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
-- Fixture 4 — an unreachable recursive definition
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
-- Fixture 5 — an `rcfgPrefix` boundary
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
-- Axiom footprint of the principal soundness theorem
-- (expect only the standard Mathlib axioms, no `sorryAx`).
------------------------------------------------------------------------

#print axioms graphHead_sound
#print axioms graphHeadUnion_sound
#print axioms headCollect_headSub_spec_sound
#print axioms headCollect_root_spec_sound
#print axioms headCollect_node_spec_sound
#print axioms graphHead_sound_of_supported

end DyNetKAT.DyNetKAT.GraphHeadTests
