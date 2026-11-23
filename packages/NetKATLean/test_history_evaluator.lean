import NetKATLean

------------------------------------------------------------------------
-- Checks for the history-level executable evaluator (H4)
-- (`DyNetKAT.NetKAT.HistoryEvaluator`).
--
-- Run with:  lake env lean test_history_evaluator.lean   (from lean/)
--
-- The evaluator is a thin adapter over the packet-level `execute`:
-- every output packet τ is paired with the UNCHANGED original history
-- tail.  The primary acceptance criterion is the Lean correctness
-- theorem `executeHistory_correct`, which is used below to establish
-- correspondence with `HistorySemantics` for every tested policy
-- (identity, drop, tests, assignment, union, sequence, Kleene star,
-- nested Kleene star, and a mixed expression).  Concrete supported-set
-- equalities and `#eval` checks are secondary evidence.
--
-- All history fixtures are the existing two-packet histories
-- (`examplePacket :: [examplePacket9]` and variants).
------------------------------------------------------------------------

open DyNetKAT.NetKAT

------------------------------------------------------------------------
-- Fixtures: two-packet histories
------------------------------------------------------------------------

-- The singleton history `examplePacket :: ⟨⟩`.
def hSingle : History := History.singleton examplePacket

-- The two-packet history `examplePacket :: [examplePacket9]`.
def hTwo : History := ⟨examplePacket, [examplePacket9]⟩

-- A second two-packet history with head `examplePacket9`.
def hTwo9 : History := ⟨examplePacket9, [examplePacket]⟩

-- Head updated to tpSrc = v9; second packet preserved verbatim.
def hTwoUpdated : History :=
  ⟨Packet.update examplePacket .tpSrc .v9, [examplePacket9]⟩

-- Head updated to tpDst = v1; second packet preserved verbatim.
def hTwoDst1 : History :=
  ⟨Packet.update examplePacket .tpDst .v1, [examplePacket9]⟩

-- Head updated twice (tpSrc = v9, then tpDst = v1); tail preserved.
def hTwoBoth : History :=
  ⟨Packet.update (Packet.update examplePacket .tpSrc .v9) .tpDst .v1,
    [examplePacket9]⟩

example : hTwo.head = examplePacket := rfl
example : hTwo.tail = [examplePacket9] := rfl
example : hSingle.toList = [examplePacket] := rfl
example : hTwoUpdated.tail = [examplePacket9] := rfl
example : hTwoDst1.tail = [examplePacket9] := rfl
example : hTwoBoth.tail = [examplePacket9] := rfl

------------------------------------------------------------------------
-- Helper: the executable second-stage fold over a singleton
-- intermediate set computes exactly the execution on that packet.
------------------------------------------------------------------------

theorem evalSeq_single (q : NetKAT) (σ τ : CtxPkt)
    (h : execute q σ = .supported {τ}) :
    evalSeq q ({σ} : Finset CtxPkt).1 = .supported {τ} := by
  have hv : ({σ} : Finset CtxPkt).1 = σ ::ₘ 0 := rfl
  simp only [hv, evalSeq, Multiset.foldr_cons, h]
  show EvalResult.supported ({τ} ∪ ∅) = .supported {τ}
  rw [Finset.union_empty]

------------------------------------------------------------------------
-- 1. Identity
------------------------------------------------------------------------

-- Concrete evaluation: the two-packet history is preserved verbatim.
example : executeHistory .id hTwo = .supported {hTwo} := by
  rw [executeHistory_eq_image .id hTwo {hTwo.head} (execute_id hTwo.head),
    Finset.image_singleton]

-- Correspondence with `HistorySemantics` through the correctness theorem.
example : ∃ B : Finset History,
    executeHistory .id hTwo = .supported B ∧
    ∀ h', HistorySemantics .id hTwo h' ↔ h' ∈ B :=
  executeHistory_correct .id hTwo

-- The output set is exactly `{hTwo}`, derived through the correctness
-- theorem (both directions of the correspondence).
example : ∃ B : Finset History,
    executeHistory .id hTwo = .supported B ∧ ∀ h' : History, h' ∈ B ↔ h' = hTwo := by
  obtain ⟨B, hex, corr⟩ := executeHistory_correct .id hTwo
  refine ⟨B, hex, fun h' => ?_⟩
  constructor
  · intro hm
    exact ((historySem_id hTwo h').mp ((corr h').mpr hm)).symm
  · intro he
    subst he
    exact (corr hTwo).mp rfl

------------------------------------------------------------------------
-- 2. Drop: a supported EMPTY set (never `.unsupported`)
------------------------------------------------------------------------

example : executeHistory .drop hTwo = .supported ∅ := by
  rw [executeHistory_eq_image .drop hTwo (∅ : Finset CtxPkt)
        (execute_drop hTwo.head),
    Finset.image_empty]

-- Correspondence: `drop` produces no history at all, so the output set
-- is empty; it is nevertheless a SUPPORTED result.
example : ∃ B : Finset History,
    executeHistory .drop hTwo = .supported B ∧
    ∀ h', HistorySemantics .drop hTwo h' ↔ h' ∈ B :=
  executeHistory_correct .drop hTwo

example : executeHistory .drop hTwo ≠ .unsupported := by
  intro hc
  obtain ⟨B, hex, _⟩ := executeHistory_correct .drop hTwo
  rw [hc] at hex
  contradiction

------------------------------------------------------------------------
-- 3. A matching field test (`tpSrc = v8` holds on the head of `hTwo`)
------------------------------------------------------------------------

example : executeHistory (NetKAT.fieldTest .tpSrc .v8) hTwo =
    .supported {hTwo} := by
  rw [executeHistory_eq_image _ hTwo {hTwo.head}
        (execute_fieldTest_match .tpSrc .v8 hTwo.head rfl),
    Finset.image_singleton]

example : ∃ B : Finset History,
    executeHistory (NetKAT.fieldTest .tpSrc .v8) hTwo = .supported B ∧
    hTwo ∈ B ∧
    ∀ h', HistorySemantics (NetKAT.fieldTest .tpSrc .v8) hTwo h' ↔ h' ∈ B := by
  obtain ⟨B, hex, corr⟩ := executeHistory_correct _ hTwo
  exact ⟨B, hex,
    (corr hTwo).mp
      (historySem_test_true (Predicate.pFieldEq ⟨FieldName.tpSrc, FieldValueEnum.v8⟩)
        hTwo rfl),
    corr⟩

------------------------------------------------------------------------
-- 4. A nonmatching field test (`tpSrc = v8` fails on the head of `hTwo9`)
------------------------------------------------------------------------

example : executeHistory (NetKAT.fieldTest .tpSrc .v8) hTwo9 =
    .supported ∅ := by
  rw [executeHistory_eq_image _ hTwo9 (∅ : Finset CtxPkt)
        (execute_fieldTest_nonmatch .tpSrc .v8 hTwo9.head (by decide)),
    Finset.image_empty]

example : ∃ B : Finset History,
    executeHistory (NetKAT.fieldTest .tpSrc .v8) hTwo9 = .supported B ∧
    (∀ h' : History, h' ∉ B) ∧
    ∀ h', HistorySemantics (NetKAT.fieldTest .tpSrc .v8) hTwo9 h' ↔ h' ∈ B := by
  obtain ⟨B, hex, corr⟩ := executeHistory_correct _ hTwo9
  refine ⟨B, hex, ?_, corr⟩
  intro h' hm
  -- `h' ∈ B` would mean the failing test preserves `h'`, contradicting
  -- `satHistory` on the head packet `examplePacket9`.
  have hsat := ((corr h').mpr hm).2
  simp [satHistory, hTwo9, examplePacket9] at hsat

------------------------------------------------------------------------
-- 5. Complete test (`completeTestTpSrc8` matches the head of `hTwo`)
------------------------------------------------------------------------

example : executeHistory (.completeTest completeTestTpSrc8) hTwo =
    .supported {hTwo} := by
  have hexec : execute (.completeTest completeTestTpSrc8) hTwo.head =
      .supported {hTwo.head} := by
    have hmatch : hTwo.head = completeTestTpSrc8 := rfl
    simp [execute_completeTest, hmatch]
  rw [executeHistory_eq_image _ hTwo {hTwo.head} hexec, Finset.image_singleton]

example : ∃ B : Finset History,
    executeHistory (.completeTest completeTestTpSrc8) hTwo = .supported B ∧
    ∀ h', HistorySemantics (.completeTest completeTestTpSrc8) hTwo h' ↔ h' ∈ B :=
  executeHistory_correct _ hTwo

------------------------------------------------------------------------
-- 6. Assignment (head updated, second packet preserved)
------------------------------------------------------------------------

example : executeHistory (.assign1 .tpSrc .v9) hTwo = .supported {hTwoUpdated} := by
  rw [executeHistory_eq_image _ hTwo {Packet.update hTwo.head .tpSrc .v9}
        (execute_assign1 (schema := ctxSchema) .tpSrc .v9 hTwo.head),
    Finset.image_singleton]
  rfl

example : ∃ B : Finset History,
    executeHistory (.assign1 .tpSrc .v9) hTwo = .supported B ∧
    hTwoUpdated ∈ B ∧
    ∀ h', HistorySemantics ((.assign1 .tpSrc .v9 : NetKAT)) hTwo h' ↔ h' ∈ B := by
  obtain ⟨B, hex, corr⟩ := executeHistory_correct _ hTwo
  exact ⟨B, hex, (corr hTwoUpdated).mp rfl, corr⟩

------------------------------------------------------------------------
-- 7. Union (assignment branch fires, `drop` branch produces nothing)
------------------------------------------------------------------------

example : executeHistory (.union (.assign1 .tpSrc .v9) .drop) hTwo =
    .supported {hTwoUpdated} := by
  have hexec : execute (.union ((.assign1 .tpSrc .v9 : NetKAT)) .drop) hTwo.head =
      .supported {Packet.update hTwo.head .tpSrc .v9} := by
    rw [execute_union_supported ((.assign1 .tpSrc .v9 : NetKAT)) .drop hTwo.head
      {Packet.update hTwo.head .tpSrc .v9} ∅
      (execute_assign1 (schema := ctxSchema) .tpSrc .v9 hTwo.head) (execute_drop hTwo.head)]
    simp
  rw [executeHistory_eq_image _ hTwo _ hexec, Finset.image_singleton]
  rfl

example : ∃ B : Finset History,
    executeHistory (.union (.assign1 .tpSrc .v9) .drop) hTwo = .supported B ∧
    ∀ h', HistorySemantics (.union ((.assign1 .tpSrc .v9 : NetKAT)) .drop) hTwo h' ↔ h' ∈ B :=
  executeHistory_correct _ hTwo

------------------------------------------------------------------------
-- 8. Sequential composition: `(tpSrc ← v9) ; (tpSrc = v9)`
------------------------------------------------------------------------

example : executeHistory
    (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9)) hTwo =
    .supported {hTwoUpdated} := by
  have hexec : execute
      (.seq ((.assign1 .tpSrc .v9 : NetKAT)) (NetKAT.fieldTest .tpSrc .v9)) hTwo.head =
      .supported {Packet.update hTwo.head .tpSrc .v9} := by
    rw [execute_seq_supported ((.assign1 .tpSrc .v9 : NetKAT)) (NetKAT.fieldTest .tpSrc .v9)
      hTwo.head {Packet.update hTwo.head .tpSrc .v9}
      (execute_assign1 (schema := ctxSchema) .tpSrc .v9 hTwo.head)]
    exact evalSeq_single _ _ _
      (execute_fieldTest_match .tpSrc .v9 (Packet.update hTwo.head .tpSrc .v9)
        (Packet.get_update_same _ _ _))
  rw [executeHistory_eq_image _ hTwo _ hexec, Finset.image_singleton]
  rfl

example : ∃ B : Finset History,
    executeHistory
      (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9)) hTwo =
      .supported B ∧
    ∀ h', HistorySemantics
      (.seq ((.assign1 .tpSrc .v9 : NetKAT)) (NetKAT.fieldTest .tpSrc .v9)) hTwo h' ↔ h' ∈ B :=
  executeHistory_correct _ hTwo

------------------------------------------------------------------------
-- 9. Kleene star: `(tpSrc ← v9)*`
--
-- The packet-level bounded iteration computes the reachable set; the
-- correctness theorem transfers it to the history level.  Zero and one
-- iterations are both outputs; every output keeps the original tail.
------------------------------------------------------------------------

example : ∃ B : Finset History,
    executeHistory (.star (.assign1 .tpSrc .v9)) hTwo = .supported B ∧
    hTwo ∈ B ∧ hTwoUpdated ∈ B ∧ (∀ h' ∈ B, h'.tail = hTwo.tail) := by
  obtain ⟨B, hex, corr⟩ := executeHistory_correct _ hTwo
  refine ⟨B, hex, (corr hTwo).mp (historySem_star_refl _ _),
    (corr hTwoUpdated).mp
      (historySem_star_step _ _ _ _ rfl (historySem_star_refl _ _)),
    fun h' hm => executeHistory_preserves_tail _ hTwo h' _ hm hex⟩

------------------------------------------------------------------------
-- 10. Nested Kleene star: `(tpSrc ← v9)**`
------------------------------------------------------------------------

example : ∃ B : Finset History,
    executeHistory (.star (.star (.assign1 .tpSrc .v9))) hTwo = .supported B ∧
    hTwo ∈ B ∧ hTwoUpdated ∈ B ∧
    ∀ h', HistorySemantics (.star (.star ((.assign1 .tpSrc .v9 : NetKAT)))) hTwo h' ↔ h' ∈ B := by
  obtain ⟨B, hex, corr⟩ := executeHistory_correct _ hTwo
  refine ⟨B, hex, (corr hTwo).mp (historySem_star_refl _ _),
    (corr hTwoUpdated).mp
      (historySem_star_step (.star (.assign1 .tpSrc .v9)) hTwo hTwoUpdated hTwoUpdated
        (historySem_star_step (.assign1 .tpSrc .v9) hTwo hTwoUpdated hTwoUpdated
          rfl (historySem_star_refl _ _))
        (historySem_star_refl _ _)),
    corr⟩

------------------------------------------------------------------------
-- 11. A mixed expression combining sequence, union and star:
--     `star ((tpSrc ← v9 + 0) ; (tpDst ← v1)*)`
------------------------------------------------------------------------

example : ∃ B : Finset History,
    executeHistory
      (.star (.seq (.union (.assign1 .tpSrc .v9) .drop)
                   (.star (.assign1 .tpDst .v1)))) hTwo =
      .supported B ∧
    hTwo ∈ B ∧ hTwoUpdated ∈ B ∧ hTwoBoth ∈ B ∧ hTwo9 ∉ B := by
  obtain ⟨B, hex, corr⟩ := executeHistory_correct _ hTwo
  refine ⟨B, hex, (corr hTwo).mp (historySem_star_refl _ _),
    -- One outer iteration: the union's assignment branch fires, the
    -- inner star takes zero steps.
    (corr hTwoUpdated).mp
      (historySem_star_step
        (.seq (.union (.assign1 .tpSrc .v9) .drop) (.star (.assign1 .tpDst .v1)))
        hTwo hTwoUpdated hTwoUpdated
        ⟨hTwoUpdated, Or.inl rfl, historySem_star_refl _ _⟩
        (historySem_star_refl _ _)),
    -- One outer iteration through the inner star: tpSrc = v9, then
    -- tpDst = v1.
    (corr hTwoBoth).mp
      (historySem_star_step
        (.seq (.union (.assign1 .tpSrc .v9) .drop) (.star (.assign1 .tpDst .v1)))
        hTwo hTwoBoth hTwoBoth
        ⟨hTwoUpdated, Or.inl rfl,
          historySem_star_step (.assign1 .tpDst .v1) hTwoUpdated hTwoBoth hTwoBoth
            rfl (historySem_star_refl _ _)⟩
        (historySem_star_refl _ _)),
    ?_⟩
  -- Nonmember: every output keeps the original tail `[examplePacket9]`,
  -- but `hTwo9` has tail `[examplePacket]`.
  intro hm
  have ht := historySemantics_preserves_tail _ hTwo hTwo9 ((corr hTwo9).mpr hm)
  have ht' : [examplePacket] = [examplePacket9] := ht
  injection ht' with e
  exact absurd (congrFun e FieldName.tpSrc) (by decide)

------------------------------------------------------------------------
-- Explicit tail preservation after MULTIPLE iterations of a nontrivial
-- policy: the original second packet `examplePacket9` remains unchanged.
--
-- The policy `(tpSrc ← v9 + tpDst ← v1)*` iterated twice updates the
-- head twice (first tpSrc = v9, then tpDst = v1); the correctness
-- theorem puts the resulting history into the evaluator's output set,
-- and `executeHistory_preserves_tail` proves its tail equals the
-- original `[examplePacket9]`.
------------------------------------------------------------------------

-- Two iterations of the union-of-assignments star reach `hTwoBoth`.
example : HistorySemantics
    (.star (.union ((.assign1 .tpSrc .v9 : NetKAT)) ((.assign1 .tpDst .v1 : NetKAT)))) hTwo hTwoBoth :=
  historySem_star_step _ _ _ _ (Or.inl rfl)
    (historySem_star_step _ _ _ _ (Or.inr rfl) (historySem_star_refl _ _))

-- `hTwoBoth` is therefore in the evaluator's output set, and its tail
-- is the ORIGINAL second packet `examplePacket9`.
example : ∃ B : Finset History,
    executeHistory
      (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpDst .v1))) hTwo =
      .supported B ∧
    hTwoBoth ∈ B ∧ hTwoBoth.tail = hTwo.tail := by
  obtain ⟨B, hex, corr⟩ := executeHistory_correct
    (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpDst .v1))) hTwo
  have hm : hTwoBoth ∈ B := (corr hTwoBoth).mp
    (historySem_star_step _ _ _ _ (Or.inl rfl)
      (historySem_star_step _ _ _ _ (Or.inr rfl) (historySem_star_refl _ _)))
  exact ⟨B, hex, hm, executeHistory_preserves_tail _ hTwo hTwoBoth _ hm hex⟩

example : hTwoBoth.tail = [examplePacket9] := rfl

-- The singleton history is handled by the same adapter.
example : executeHistory (.assign1 .tpSrc .v9) hSingle =
    .supported {⟨Packet.update examplePacket .tpSrc .v9, []⟩} := by
  rw [executeHistory_eq_image _ hSingle {Packet.update hSingle.head .tpSrc .v9}
    (execute_assign1 (schema := ctxSchema) .tpSrc .v9 hSingle.head), Finset.image_singleton]
  rfl

------------------------------------------------------------------------
-- Output characterization: the generated histories are exactly the
-- packet-evaluator outputs paired with the original tail.
------------------------------------------------------------------------

example (p : NetKAT) (h : History) (B : Finset History)
    (heval : executeHistory p h = .supported B) (h' : History) :
    h' ∈ B ↔ ∃ τ : CtxPkt, Semantics p h.head τ ∧ h' = ⟨τ, h.tail⟩ :=
  executeHistory_outputs_characterization p h B heval h'

-- Concretely: the assignment's output history is the updated head
-- packet paired with the original tail.
example : ∃ τ : CtxPkt,
    Semantics ((.assign1 .tpSrc .v9 : NetKAT)) hTwo.head τ ∧ hTwoUpdated = ⟨τ, hTwo.tail⟩ := by
  obtain ⟨B, hex, corr⟩ := executeHistory_correct (.assign1 .tpSrc .v9) hTwo
  have hmem : hTwoUpdated ∈ B := (corr hTwoUpdated).mp rfl
  exact (executeHistory_outputs_characterization _ hTwo _ hex hTwoUpdated).mp hmem

------------------------------------------------------------------------
-- Executable checks (secondary evidence; the proofs above are primary)
--
-- Kleene-star policies are NOT exercised by `#eval`: their bounded
-- iteration (256 steps over the concrete packet space) overflows the
-- Lean interpreter stack, so — exactly like the existing
-- `test_evaluator_integration.lean` — stars are covered exclusively
-- through the correctness-theorem proofs above.
------------------------------------------------------------------------

#eval decide (executeHistory .id hTwo = HistoryEvalResult.supported {hTwo})       -- true
#eval decide (executeHistory .drop hTwo =
  HistoryEvalResult.supported (∅ : Finset History))                               -- true
#eval decide (executeHistory (NetKAT.fieldTest .tpSrc .v8) hTwo =
  HistoryEvalResult.supported {hTwo})                                             -- true
#eval decide (executeHistory (NetKAT.fieldTest .tpSrc .v8) hTwo9 =
  HistoryEvalResult.supported (∅ : Finset History))                               -- true
#eval decide (executeHistory (.assign1 .tpSrc .v9) hTwo =
  HistoryEvalResult.supported {hTwoUpdated})                                      -- true
#eval decide (executeHistory (.union (.assign1 .tpSrc .v9) .drop) hTwo =
  HistoryEvalResult.supported {hTwoUpdated})                                      -- true
#eval decide (executeHistory
  (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9)) hTwo =
  HistoryEvalResult.supported {hTwoUpdated})                                      -- true

-- Axiom check: the main theorem depends on no new axioms and no `sorryAx`.
#print axioms executeHistory_correct
