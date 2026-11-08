import DyNetKAT

namespace DyNetKAT.NetKAT

def composedPolicy : NetKAT :=
  .seq (.test Predicate.tpSrc8)
    (.seq (.assign1 .tpDst .v1)
      (.union .id (.assign1 .port .v9)))

def starPolicy : NetKAT := .star (.assign1 .tpSrc .v9)

/- The public umbrella import exposes the correctness theorem for a composed
   policy using predicate tests, assignment, sequencing, and union. -/
example : ∃ B : Finset CtxPkt,
    execute composedPolicy examplePacket = .supported B ∧
      ∀ τ, Semantics composedPolicy examplePacket τ ↔ τ ∈ B := by
  exact execute_correct composedPolicy examplePacket

/- Kleene star is covered through the same public correctness theorem. -/
example : ∃ B : Finset CtxPkt,
    execute starPolicy examplePacket = .supported B ∧
      ∀ τ, Semantics starPolicy examplePacket τ ↔ τ ∈ B := by
  exact execute_correct starPolicy examplePacket

/- A concrete executable check for a primitive assignment. -/
example :
    execute (.assign1 .tpDst .v1) examplePacket =
      .supported {Packet.update examplePacket .tpDst .v1} := by
  exact execute_assign1 .tpDst .v1 examplePacket

end DyNetKAT.NetKAT

------------------------------------------------------------------------
-- H5A regression: the packet-processing SOS migrated to history semantics
--
-- `Step.cpol_seq_ok` now requires the singleton-history premise
--   HistorySemantics p (History.singleton σ) (History.singleton σ')
-- and `packetTransitions` evaluates through the verified history-level
-- evaluator `executeHistory p (History.singleton σ)`.  These tests pin the
-- observable packet-processing behavior: same actions, same destination
-- configurations, same pending-tail and handled order, same continuation,
-- and the same unsupported / supported-empty distinction.
------------------------------------------------------------------------

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

/-- A distinctive continuation so the tests can observe that it is
    preserved verbatim. -/
def testContinuation : DyNetKAT := .nSeq NetKAT.id .deadlock

/-- Local helper: the executable second-stage fold over a singleton
    intermediate set computes exactly the execution on that packet. -/
theorem evalSeq_single (q : NetKAT) (σ τ : CtxPkt)
    (h : execute q σ = .supported {τ}) :
    evalSeq q ({σ} : Finset CtxPkt).1 = .supported {τ} := by
  have hv : ({σ} : Finset CtxPkt).1 = σ ::ₘ 0 := rfl
  simp only [hv, evalSeq, Multiset.foldr_cons, h]
  show EvalResult.supported ({τ} ∪ ∅) = .supported {τ}
  rw [Finset.union_empty]

/-- The updated packet of `tpSrc ← v9` on the example packet is the
    `v9` example packet. -/
example : Packet.update examplePacket .tpSrc .v9 = examplePacket9 := by
  funext f'
  cases f' <;> simp [Packet.update, examplePacket, examplePacket9]

------------------------------------------------------------------------
-- 1. `id` produces exactly the previous packet-processing transition.
------------------------------------------------------------------------

example :
    packetTransitions NetKAT.id .deadlock [examplePacket] [] =
      some {((Action.packet examplePacket examplePacket,
        ({ proc := .deadlock, pending := [], handled := [examplePacket] } : Config))
        : Action × Config)} := by
  have h1 : executeHistory NetKAT.id (History.singleton examplePacket) =
      .supported (({examplePacket} : Finset CtxPkt).image
        fun τ => (⟨τ, []⟩ : History)) :=
    executeHistory_eq_image NetKAT.id (History.singleton examplePacket) {examplePacket}
      (execute_id examplePacket)
  simp [packetTransitions, h1, Finset.image_singleton, Multiset.map_singleton]

------------------------------------------------------------------------
-- 2. `drop` produces zero transitions (a supported empty result).
------------------------------------------------------------------------

private theorem packetTransitions_drop_example :
    packetTransitions NetKAT.drop .deadlock [examplePacket] [] =
      some (∅ : Multiset (Action × Config)) := by
  have h1 : executeHistory NetKAT.drop (History.singleton examplePacket) =
      .supported ((∅ : Finset CtxPkt).image fun τ => (⟨τ, []⟩ : History)) :=
    executeHistory_eq_image NetKAT.drop (History.singleton examplePacket) ∅
      (execute_drop examplePacket)
  simp [packetTransitions, h1, Finset.image_empty, Finset.empty_val,
    Multiset.map_zero]

example : packetTransitions NetKAT.drop .deadlock [examplePacket] [] =
  some (∅ : Multiset (Action × Config)) :=
  packetTransitions_drop_example

------------------------------------------------------------------------
-- 3. A matching field test produces the expected transition.
------------------------------------------------------------------------

example :
    packetTransitions (NetKAT.fieldTest .tpSrc .v8) .deadlock [examplePacket] [] =
      some {((Action.packet examplePacket examplePacket,
        ({ proc := .deadlock, pending := [], handled := [examplePacket] } : Config))
        : Action × Config)} := by
  have h1 : executeHistory (NetKAT.fieldTest .tpSrc .v8)
      (History.singleton examplePacket) =
      .supported (({examplePacket} : Finset CtxPkt).image
        fun τ => (⟨τ, []⟩ : History)) :=
    executeHistory_eq_image _ (History.singleton examplePacket) {examplePacket}
      (execute_fieldTest_match .tpSrc .v8 examplePacket rfl)
  simp [packetTransitions, h1, Finset.image_singleton, Multiset.map_singleton]

------------------------------------------------------------------------
-- 4. A nonmatching field test produces zero transitions.
------------------------------------------------------------------------

example :
    packetTransitions (NetKAT.fieldTest .tpSrc .v9) .deadlock [examplePacket] [] =
      some (∅ : Multiset (Action × Config)) := by
  have h1 : executeHistory (NetKAT.fieldTest .tpSrc .v9)
      (History.singleton examplePacket) =
      .supported ((∅ : Finset CtxPkt).image fun τ => (⟨τ, []⟩ : History)) :=
    executeHistory_eq_image _ (History.singleton examplePacket) ∅
      (execute_fieldTest_nonmatch .tpSrc .v9 examplePacket (by decide))
  simp [packetTransitions, h1, Finset.image_empty, Finset.empty_val,
    Multiset.map_zero]

------------------------------------------------------------------------
-- 5. Assignment produces the expected updated packet.
------------------------------------------------------------------------

example :
    packetTransitions (.assign1 .tpSrc .v9) .deadlock [examplePacket] [] =
      some {((Action.packet examplePacket (Packet.update examplePacket .tpSrc .v9),
        ({ proc := .deadlock, pending := [],
           handled := [Packet.update examplePacket .tpSrc .v9] } : Config))
        : Action × Config)} := by
  have h1 : executeHistory (.assign1 .tpSrc .v9) (History.singleton examplePacket) =
      .supported (({Packet.update examplePacket .tpSrc .v9} : Finset CtxPkt).image
        fun τ => (⟨τ, []⟩ : History)) :=
    executeHistory_eq_image _ (History.singleton examplePacket) _
      (execute_assign1 .tpSrc .v9 examplePacket)
  simp [packetTransitions, h1, Finset.image_singleton, Multiset.map_singleton]

------------------------------------------------------------------------
-- 6. Union produces the expected transitions: exactly two, and both
--    expected packet actions and destinations appear.
------------------------------------------------------------------------

example :
    (packetTransitions (.union .id (.assign1 .tpSrc .v9)) .deadlock
      [examplePacket] []).map Multiset.card = some 2 := by
  native_decide

example : ∃ results : Multiset (Action × Config),
    packetTransitions (.union .id (.assign1 .tpSrc .v9)) .deadlock
      [examplePacket] [] = some results ∧
    (Action.packet examplePacket examplePacket,
      ({ proc := .deadlock, pending := [], handled := [examplePacket] } : Config))
        ∈ results ∧
    (Action.packet examplePacket (Packet.update examplePacket .tpSrc .v9),
      ({ proc := .deadlock, pending := [],
         handled := [Packet.update examplePacket .tpSrc .v9] } : Config))
        ∈ results := by
  obtain ⟨B, hB, corr⟩ := execute_correct (.union .id (.assign1 .tpSrc .v9))
    examplePacket
  have h1 : executeHistory (.union .id (.assign1 .tpSrc .v9))
      (History.singleton examplePacket) =
      .supported (B.image fun τ => (⟨τ, []⟩ : History)) :=
    executeHistory_eq_image _ (History.singleton examplePacket) B hB
  have hex : packetTransitions (.union .id (.assign1 .tpSrc .v9)) .deadlock
      [examplePacket] [] =
      some ((B.image fun τ => (⟨τ, []⟩ : History)).1.map fun h' =>
        (Action.packet examplePacket h'.head,
          { proc := .deadlock, pending := [],
            handled := h'.head :: ([] : List CtxPkt) })) := by
    simp [packetTransitions, h1]
  refine ⟨_, hex, ?_, ?_⟩
  · apply Multiset.mem_map.mpr
    refine ⟨⟨examplePacket, []⟩, ?_, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨examplePacket, (corr examplePacket).mp
        ((union_sem .id (.assign1 .tpSrc .v9) examplePacket examplePacket).mpr
          (Or.inl rfl)), rfl⟩)
  · apply Multiset.mem_map.mpr
    refine ⟨⟨Packet.update examplePacket .tpSrc .v9, []⟩, ?_, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨Packet.update examplePacket .tpSrc .v9,
        (corr (Packet.update examplePacket .tpSrc .v9)).mp
          ((union_sem .id (.assign1 .tpSrc .v9) examplePacket _).mpr
            (Or.inr ((assign1_sem .tpSrc .v9 examplePacket _).mpr rfl))),
        rfl⟩)

------------------------------------------------------------------------
-- 7. Sequence preserves the continuation, the pending-tail order, and the
--    handled order (new packet prepended, old handled kept verbatim).
------------------------------------------------------------------------

example :
    packetTransitions (.seq (.assign1 .tpSrc .v9) .id) testContinuation
        [examplePacket, examplePacket9] [examplePacket] =
      some {((Action.packet examplePacket (Packet.update examplePacket .tpSrc .v9),
        ({ proc := testContinuation, pending := [examplePacket9],
           handled := [Packet.update examplePacket .tpSrc .v9, examplePacket] } : Config))
        : Action × Config)} := by
  have hexec : execute (.seq (.assign1 .tpSrc .v9) .id) examplePacket =
      .supported {Packet.update examplePacket .tpSrc .v9} := by
    rw [execute_seq_supported (.assign1 .tpSrc .v9) NetKAT.id examplePacket
      {Packet.update examplePacket .tpSrc .v9}
      (execute_assign1 .tpSrc .v9 examplePacket)]
    exact evalSeq_single NetKAT.id (Packet.update examplePacket .tpSrc .v9) _
      (execute_id _)
  have h1 : executeHistory (.seq (.assign1 .tpSrc .v9) .id)
      (History.singleton examplePacket) =
      .supported (({Packet.update examplePacket .tpSrc .v9} : Finset CtxPkt).image
        fun τ => (⟨τ, []⟩ : History)) :=
    executeHistory_eq_image _ (History.singleton examplePacket) _ hexec
  simp [packetTransitions, h1, Finset.image_singleton, Multiset.map_singleton]

------------------------------------------------------------------------
-- 8. Kleene star produces the expected transitions: zero iterations
--    (σ → σ) and one iteration (σ → σ[f:=v9]).
------------------------------------------------------------------------

example : ∃ results : Multiset (Action × Config),
    packetTransitions (.star (.assign1 .tpSrc .v9)) .deadlock [examplePacket] [] =
      some results ∧
    (Action.packet examplePacket examplePacket,
      ({ proc := .deadlock, pending := [], handled := [examplePacket] } : Config))
        ∈ results ∧
    (Action.packet examplePacket (Packet.update examplePacket .tpSrc .v9),
      ({ proc := .deadlock, pending := [],
         handled := [Packet.update examplePacket .tpSrc .v9] } : Config))
        ∈ results := by
  obtain ⟨B, hB, corr⟩ := execute_correct (.star (.assign1 .tpSrc .v9)) examplePacket
  have h1 : executeHistory (.star (.assign1 .tpSrc .v9))
      (History.singleton examplePacket) =
      .supported (B.image fun τ => (⟨τ, []⟩ : History)) :=
    executeHistory_eq_image _ (History.singleton examplePacket) B hB
  have hex : packetTransitions (.star (.assign1 .tpSrc .v9)) .deadlock
      [examplePacket] [] =
      some ((B.image fun τ => (⟨τ, []⟩ : History)).1.map fun h' =>
        (Action.packet examplePacket h'.head,
          { proc := .deadlock, pending := [],
            handled := h'.head :: ([] : List CtxPkt) })) := by
    simp [packetTransitions, h1]
  refine ⟨_, hex, ?_, ?_⟩
  · apply Multiset.mem_map.mpr
    refine ⟨⟨examplePacket, []⟩, ?_, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨examplePacket, (corr examplePacket).mp (star_refl _ examplePacket), rfl⟩)
  · apply Multiset.mem_map.mpr
    refine ⟨⟨Packet.update examplePacket .tpSrc .v9, []⟩, ?_, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨Packet.update examplePacket .tpSrc .v9,
        (corr (Packet.update examplePacket .tpSrc .v9)).mp
          (star_step (.assign1 .tpSrc .v9) examplePacket _
            ((assign1_sem .tpSrc .v9 examplePacket _).mpr rfl)),
        rfl⟩)

------------------------------------------------------------------------
-- 9. Nested Kleene star works: the same two expected transitions.
------------------------------------------------------------------------

example : ∃ results : Multiset (Action × Config),
    packetTransitions (.star (.star (.assign1 .tpSrc .v9))) .deadlock
      [examplePacket] [] = some results ∧
    (Action.packet examplePacket examplePacket,
      ({ proc := .deadlock, pending := [], handled := [examplePacket] } : Config))
        ∈ results ∧
    (Action.packet examplePacket (Packet.update examplePacket .tpSrc .v9),
      ({ proc := .deadlock, pending := [],
         handled := [Packet.update examplePacket .tpSrc .v9] } : Config))
        ∈ results := by
  obtain ⟨B, hB, corr⟩ :=
    execute_correct (.star (.star (.assign1 .tpSrc .v9))) examplePacket
  have h1 : executeHistory (.star (.star (.assign1 .tpSrc .v9)))
      (History.singleton examplePacket) =
      .supported (B.image fun τ => (⟨τ, []⟩ : History)) :=
    executeHistory_eq_image _ (History.singleton examplePacket) B hB
  have hex : packetTransitions (.star (.star (.assign1 .tpSrc .v9))) .deadlock
      [examplePacket] [] =
      some ((B.image fun τ => (⟨τ, []⟩ : History)).1.map fun h' =>
        (Action.packet examplePacket h'.head,
          { proc := .deadlock, pending := [],
            handled := h'.head :: ([] : List CtxPkt) })) := by
    simp [packetTransitions, h1]
  refine ⟨_, hex, ?_, ?_⟩
  · apply Multiset.mem_map.mpr
    refine ⟨⟨examplePacket, []⟩, ?_, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨examplePacket, (corr examplePacket).mp (star_refl _ examplePacket), rfl⟩)
  · apply Multiset.mem_map.mpr
    refine ⟨⟨Packet.update examplePacket .tpSrc .v9, []⟩, ?_, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨Packet.update examplePacket .tpSrc .v9,
        (corr (Packet.update examplePacket .tpSrc .v9)).mp
          (star_step (.star (.assign1 .tpSrc .v9)) examplePacket _
            (star_step (.assign1 .tpSrc .v9) examplePacket _
              ((assign1_sem .tpSrc .v9 examplePacket _).mpr rfl))),
        rfl⟩)

------------------------------------------------------------------------
-- 10. The unsupported / supported-empty distinction remains intact.
--
--     A supported empty evaluation yields `some ∅` (never `none`), and an
--     unsupported history evaluation yields `none`.
------------------------------------------------------------------------

example : packetTransitions NetKAT.drop .deadlock [examplePacket] [] ≠ none := by
  simp [packetTransitions_drop_example]

example (p : NetKAT) (continuation : DyNetKAT) (σ : CtxPkt)
    (hun : executeHistory p (History.singleton σ) = .unsupported) :
    packetTransitions p continuation [σ] [] = none := by
  simp [packetTransitions, hun]

------------------------------------------------------------------------
-- The public `DyNetKAT` import exposes the migrated SOS rule and its
-- history-based bridge: `Step.cpol_seq_ok` is directly applicable with the
-- singleton-history premise, and the bridge theorem derives it from the
-- history evaluator.
------------------------------------------------------------------------

example (env : RecEnv) (q : DyNetKAT) (pendingTail handled : List CtxPkt) :
    Step env
      ({ proc := .nSeq NetKAT.id q,
         pending := examplePacket :: pendingTail,
         handled := handled } : Config)
      (Action.packet examplePacket examplePacket)
      ({ proc := q,
         pending := pendingTail,
         handled := examplePacket :: handled } : Config) :=
  Step.cpol_seq_ok NetKAT.id q examplePacket examplePacket pendingTail handled
    ((historySemantics_singleton_iff_packetSemantics NetKAT.id examplePacket
      examplePacket).mpr rfl)

example (env : RecEnv) (continuation : DyNetKAT) (pendingTail handled : List CtxPkt) :
    Step env
      ({ proc := .nSeq NetKAT.id continuation,
         pending := examplePacket :: pendingTail,
         handled := handled } : Config)
      (Action.packet examplePacket examplePacket)
      ({ proc := continuation,
         pending := pendingTail,
         handled := examplePacket :: handled } : Config) :=
  executeHistory_packet_step env NetKAT.id continuation examplePacket
    (History.singleton examplePacket) pendingTail handled
    (({examplePacket} : Finset CtxPkt).image fun τ => (⟨τ, []⟩ : History))
    (executeHistory_eq_image NetKAT.id (History.singleton examplePacket)
      {examplePacket} (execute_id examplePacket))
    (Finset.mem_image.mpr ⟨examplePacket, Finset.mem_singleton.mpr rfl, rfl⟩)

end DyNetKAT.DyNetKAT
