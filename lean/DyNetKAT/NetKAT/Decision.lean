import DyNetKAT.NetKAT.Evaluator
import DyNetKAT.NetKAT.HistorySemantics
import DyNetKAT.NetKAT.Symbolic

/-! The public NetKAT equality and zero checks use the verified native
symbolic frontend. The pointwise API supports concrete execution certificates. -/

namespace DyNetKAT.NetKAT

------------------------------------------------------------------------
-- Decidable equality on packets
------------------------------------------------------------------------

/-- Decidable equality on the concrete packet space, via the explicit
    field enumeration (same construction as the file-local instances in
    `Evaluator.lean` and `Executable.lean`, registered here as a global
    instance so that the checker and downstream executable checks can
    compare output sets). -/
instance instDecEqCtxPkt : DecidableEq CtxPkt := ctxSchema.packetEq

-- Complete tests reuse packet equality. Policy equality is syntactic.
instance : DecidableEq CompleteTest := instDecEqCtxPkt

section
local instance {schema : PacketSchema} : DecidableEq schema.Field := schema.fieldEq
local instance {schema : PacketSchema} (f : schema.Field) : DecidableEq (schema.Value f) :=
  schema.valueEq f
local instance {schema : PacketSchema} : DecidableEq schema.Packet := schema.packetEq

deriving instance DecidableEq for NetKAT
end

------------------------------------------------------------------------
-- The equivalence checker
------------------------------------------------------------------------

/-- Pointwise comparison of the two computed output sets on one input
    packet.

    A supported empty output set is compared like any other set, while an
    `unsupported` result on either side yields `false`; the distinction
    between `.unsupported` and `.supported ∅` is therefore preserved. -/
def netkatEquivAt (p q : NetKAT) (σ : CtxPkt) : Bool :=
  match execute p σ, execute q σ with
  | .supported A, .supported B => decide (A = B)
  | _, _ => false

------------------------------------------------------------------------
-- Correctness of the checker
------------------------------------------------------------------------

/-- On supported executions, the pointwise check is exactly equality of
    the two computed output sets. -/
theorem netkatEquivAt_supported (p q : NetKAT) (σ : CtxPkt) (A B : Finset CtxPkt)
    (hA : execute p σ = .supported A) (hB : execute q σ = .supported B) :
    netkatEquivAt p q σ = decide (A = B) := by
  show (match execute p σ, execute q σ with
    | .supported A, .supported B => decide (A = B)
    | _, _ => false) = decide (A = B)
  rw [hA, hB]

/-- Soundness of the pointwise check: a positive per-packet result implies
    that both policies relate the input packet to exactly the same output
    packets. -/
theorem netkatEquivAt_sound (p q : NetKAT) (σ : CtxPkt)
    (h : netkatEquivAt p q σ = true) :
    ∀ τ, Semantics p σ τ ↔ Semantics q σ τ := by
  obtain ⟨A, hA, corrA⟩ := execute_correct p σ
  obtain ⟨B, hB, corrB⟩ := execute_correct q σ
  rw [netkatEquivAt_supported p q σ A B hA hB] at h
  have hAB : A = B := decide_eq_true_iff.mp h
  intro τ
  rw [corrA τ, corrB τ, hAB]

/-- Completeness of the pointwise check: whenever both policies relate the
    input packet to exactly the same output packets, the per-packet check
    succeeds. -/
theorem netkatEquivAt_complete (p q : NetKAT) (σ : CtxPkt)
    (h : ∀ τ, Semantics p σ τ ↔ Semantics q σ τ) :
    netkatEquivAt p q σ = true := by
  obtain ⟨A, hA, corrA⟩ := execute_correct p σ
  obtain ⟨B, hB, corrB⟩ := execute_correct q σ
  rw [netkatEquivAt_supported p q σ A B hA hB]
  refine decide_eq_true ?_
  ext τ
  rw [← corrA τ, ← corrB τ]
  exact h τ

/-- Core dup-free NetKAT equivalence. -/
def netkatEquiv (p q : NetKAT) : Bool :=
  netkatNativeEquiv p q

theorem netkatEquiv_correct (p q : NetKAT) :
    netkatEquiv p q = true ↔ ∀ σ τ : CtxPkt, Semantics p σ τ ↔ Semantics q σ τ :=
  netkatNativeEquiv_correct p q

------------------------------------------------------------------------
-- The zero checker
------------------------------------------------------------------------

/-- `Semantics .drop` is the empty relation: no packet pair is related. -/
theorem sem_drop_false (σ τ : CtxPkt) : ¬ Semantics (schema := ctxSchema) .drop σ τ := by
  simp [Semantics]

/-- NetKAT zero checker: decides whether the policy `p` denotes the empty
    relation on the finite packet domain.

    The check reuses the verified equivalence checker against `drop`, whose
    relational semantics is empty; no separate packet-enumeration logic is
    introduced. -/
def netkatIsZero {schema : PacketSchema} (p : NetKAT schema) : Bool :=
  netkatNativeEquivFinite p .drop

/-- Main correctness theorem for the zero checker: the checker returns `true`
    exactly when `p` relates no input packet to any output packet, i.e. its
    relational semantics over the finite packet domain is empty. -/
theorem netkatIsZero_correct
    {schema : PacketSchema} (p : NetKAT schema) :
    netkatIsZero p = true ↔
      ∀ σ τ : schema.Packet,
        ¬ Semantics p σ τ := by
  unfold netkatIsZero
  rw [netkatNativeEquivFinite_correct]
  constructor
  · intro h σ τ hp
    exact (h σ τ).mp hp
  · intro h σ τ
    constructor
    · intro hp
      exact absurd hp (h σ τ)
    · intro hd
      exact False.elim hd

/-- The evaluator gives every output history by replacing its input head
    with one of the computed packets and retaining the input tail. -/
theorem execute_history_correct (p : NetKAT) (σ : CtxPkt) :
    ∃ B : Finset CtxPkt, execute p σ = .supported B ∧
      ∀ τ (h h' : List CtxPkt),
        HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔ h' = h ∧ τ ∈ B := by
  obtain ⟨B, hB, hSem⟩ := execute_correct p σ
  exact ⟨B, hB, fun τ h h' =>
    (historySemantics_iff_packetSemantics p σ τ h h').trans
      (and_congr_right fun _ => hSem τ)⟩

/-- Equivalence of dup-free policies on all histories over the same packet
    universe. Singleton histories recover the packet relation. -/
theorem netkatEquiv_history_correct (p q : NetKAT) :
    netkatEquiv p q = true ↔
      ∀ h h' : History, HistorySemantics p h h' ↔ HistorySemantics q h h' := by
  rw [netkatEquiv_correct]
  constructor
  · rintro hpq ⟨σ, h⟩ ⟨τ, h'⟩
    rw [historySemantics_iff_packetSemantics p σ τ h h',
      historySemantics_iff_packetSemantics q σ τ h h', hpq σ τ]
  · intro hpq σ τ
    have histories := hpq ⟨σ, []⟩ ⟨τ, []⟩
    rw [historySemantics_iff_packetSemantics p σ τ [] [],
      historySemantics_iff_packetSemantics q σ τ [] []] at histories
    exact ⟨fun hp => (histories.mp ⟨rfl, hp⟩).2,
      fun hq => (histories.mpr ⟨rfl, hq⟩).2⟩

theorem netkatIsZero_history_correct (p : NetKAT) :
    netkatIsZero p = true ↔ ∀ h h' : History, ¬ HistorySemantics p h h' := by
  rw [netkatIsZero_correct]
  constructor
  · intro zero ⟨i, tail⟩ ⟨o, tail'⟩ h
    exact zero i o ((historySemantics_iff_packetSemantics ..).mp h).2
  · intro zero i o h
    exact zero (History.singleton i) (History.singleton o)
      ((historySemantics_iff_packetSemantics ..).mpr ⟨rfl, h⟩)

/-- Elaborate the complete-test shorthand into the common NetKAT syntax
    of primitive field tests, sequencing and identity. -/
def completeTestExpr (α : CompleteTest) : NetKAT :=
  NetKAT.fieldEnum.foldr (fun f rest => .seq (NetKAT.fieldTest f (α f)) rest) .id

theorem completeTestExpr_correct (α : CompleteTest) (σ τ : CtxPkt) :
    Semantics (completeTestExpr α) σ τ ↔ Semantics (schema := ctxSchema) (.completeTest α) σ τ := by
  have fields (fs : List FieldName) :
      Semantics (schema := ctxSchema) (fs.foldr (fun f rest => .seq (NetKAT.fieldTest f (α f)) rest) .id) σ τ ↔
        (∀ f ∈ fs, σ f = α f) ∧ σ = τ := by
    induction fs with
    | nil => simp [id_diag]
    | cons f fs ih =>
        simp only [List.foldr_cons, seq_sem, fieldTest_sem]
        constructor
        · rintro ⟨ρ, ⟨hField, rfl⟩, hRest⟩
          obtain ⟨hFields, rfl⟩ := ih.mp hRest
          exact ⟨fun g hg => (List.mem_cons.mp hg).elim (fun h => h ▸ hField) (hFields g), rfl⟩
        · rintro ⟨h, rfl⟩
          exact ⟨σ, ⟨h f (by simp), rfl⟩,
            ih.mpr ⟨fun g hg => h g (List.mem_cons_of_mem _ hg), rfl⟩⟩
  rw [completeTestExpr, fields, Semantics]
  exact and_congr_left' ⟨fun h f => (h f (NetKAT.fieldEnum_complete f)).symm, fun h f _ => (h f).symm⟩

/-- Secondary characterization: a policy is zero exactly when every execution
    computes a supported empty output set. -/
theorem netkatIsZero_iff_empty_execute
    (p : NetKAT) :
    netkatIsZero p = true ↔
      ∀ σ : CtxPkt, execute p σ = .supported ∅ := by
  constructor
  · intro h
    rw [netkatIsZero_correct] at h
    intro σ
    obtain ⟨B, hB, corrB⟩ := execute_correct p σ
    rcases Finset.eq_empty_or_nonempty B with hBempty | hne
    · rw [hB, hBempty]
    · obtain ⟨τ, hτ⟩ := hne
      exact absurd ((corrB τ).mpr hτ) (h σ τ)
  · intro h
    rw [netkatIsZero_correct]
    intro σ τ hp
    obtain ⟨B, hB, corrB⟩ := execute_correct p σ
    have hBeq : B = (∅ : Finset CtxPkt) :=
      EvalResult.supported.inj (hB.symm.trans (h σ))
    subst hBeq
    exact Finset.not_mem_empty τ ((corrB τ).mp hp)

------------------------------------------------------------------------
-- Examples (checked through the verified correctness bridge)
------------------------------------------------------------------------

/-- Every policy is equivalent to itself. -/
theorem netkatEquiv_self (p : NetKAT) : netkatEquiv p p = true :=
  (netkatEquiv_correct p p).mpr fun _ _ => Iff.rfl

/-- `drop` and the always-false predicate test are semantically equivalent. -/
theorem netkatEquiv_drop_pFalse : netkatEquiv .drop (.test .pFalse) = true := by
  refine (netkatEquiv_correct .drop (.test .pFalse)).mpr ?_
  intro σ τ
  simp [Semantics, Predicate.holds, Predicate.eval]

/-- `id` and `drop` are not semantically equivalent. -/
theorem netkatEquiv_id_drop_false : netkatEquiv .id .drop = false := by
  have hne : ¬ (netkatEquiv .id .drop = true) := by
    intro h
    exact (((netkatEquiv_correct .id .drop).mp h) examplePacket examplePacket).1 rfl
  exact Bool.eq_false_iff.mpr hne

end DyNetKAT.NetKAT
