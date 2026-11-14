------------------------------------------------------------------------
-- Verified NetKAT semantic-equivalence and zero checkers (finite packet
-- domain)
--
-- `netkatEquiv p q` decides whether the dup-free NetKAT policies `p` and
-- `q` have identical relational semantics on the existing finite packet
-- domain `CtxPkt`.  Both policies are executed on every packet of the
-- finite domain (no hardcoded domain size: the enumeration comes from the
-- existing `Fintype CtxPkt` instance) and their complete computed output
-- sets are compared.  The evaluator's `unsupported` result is kept
-- distinct from a supported empty output set.
--
-- `netkatEquiv_correct` relates the Boolean result unconditionally to
-- semantic equivalence, reusing `execute_correct` from `Evaluator.lean`.
-- Both directions are proved; no new axioms are introduced.
--
-- The zero checker `netkatIsZero p` decides whether `p` denotes the empty
-- relation by reusing `netkatEquiv` against `drop`; `netkatIsZero_correct`
-- relates the Boolean result unconditionally to emptiness of the relational
-- semantics over the finite packet domain.
--
-- Scope boundary: the theorem establishes semantic equivalence for the
-- existing finite-domain, dup-free NetKAT AST only.  It does NOT
-- establish derivability in `E_NK`, completeness of the `E_NK` axiom
-- system, DyNetKAT bisimilarity, safety of arbitrary DyNetKAT systems,
-- or scalability to realistic packet domains.
--
-- Note: this Mathlib snapshot (v4.19.0) has no `Finset.all`, so the
-- checker is expressed as a decidable universal check over the packet
-- universe, which is computably equivalent to the intended
-- `Finset.univ.all` formulation.
------------------------------------------------------------------------

import DyNetKAT.NetKAT.Evaluator
import DyNetKAT.NetKAT.HistorySemantics

namespace DyNetKAT.NetKAT

------------------------------------------------------------------------
-- Decidable equality on packets
------------------------------------------------------------------------

/-- Decidable equality on the concrete packet space, via the explicit
    field enumeration (same construction as the file-local instances in
    `Evaluator.lean` and `Executable.lean`, registered here as a global
    instance so that the checker and downstream executable checks can
    compare output sets). -/
instance instDecEqCtxPkt : DecidableEq CtxPkt := by
  intro σ τ
  exact decidable_of_iff (∀ f ∈ NetKAT.fieldEnum, σ f = τ f) (by
    constructor
    · intro h
      funext f
      exact h f (NetKAT.fieldEnum_complete f)
    · intro h f hf
      exact congrFun h f)

-- Complete tests reuse packet equality. Policy equality is syntactic.
instance : DecidableEq CompleteTest := instDecEqCtxPkt

deriving instance DecidableEq for NetKAT

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

/-- NetKAT semantic-equivalence checker over the finite packet domain.

    Both policies are evaluated on every possible input packet and their
    complete output sets are compared; the result is `true` exactly when
    all output sets agree. -/
def netkatEquiv (p q : NetKAT) : Bool :=
  decide (∀ σ : CtxPkt, netkatEquivAt p q σ = true)

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

/-- Main correctness theorem: the checker returns `true` exactly when both
    policies have identical relational semantics on every packet of the
    finite domain. -/
theorem netkatEquiv_correct
    (p q : NetKAT) :
    netkatEquiv p q = true ↔
      ∀ σ τ : CtxPkt,
        Semantics p σ τ ↔ Semantics q σ τ := by
  constructor
  · intro h σ τ
    have h' : (∀ ν : CtxPkt, netkatEquivAt p q ν = true) := decide_eq_true_iff.mp h
    exact netkatEquivAt_sound p q σ (h' σ) τ
  · intro h
    show decide (∀ σ : CtxPkt, netkatEquivAt p q σ = true)
    exact decide_eq_true (fun σ => netkatEquivAt_complete p q σ (h σ))

------------------------------------------------------------------------
-- The zero checker
------------------------------------------------------------------------

/-- `Semantics .drop` is the empty relation: no packet pair is related. -/
theorem sem_drop_false (σ τ : CtxPkt) : ¬ Semantics .drop σ τ := by
  simp [Semantics]

/-- NetKAT zero checker: decides whether the policy `p` denotes the empty
    relation on the finite packet domain.

    The check reuses the verified equivalence checker against `drop`, whose
    relational semantics is empty; no separate packet-enumeration logic is
    introduced. -/
def netkatIsZero (p : NetKAT) : Bool :=
  netkatEquiv p .drop

/-- Main correctness theorem for the zero checker: the checker returns `true`
    exactly when `p` relates no input packet to any output packet, i.e. its
    relational semantics over the finite packet domain is empty. -/
theorem netkatIsZero_correct
    (p : NetKAT) :
    netkatIsZero p = true ↔
      ∀ σ τ : CtxPkt,
        ¬ Semantics p σ τ := by
  unfold netkatIsZero
  rw [netkatEquiv_correct]
  constructor
  · intro h σ τ hp
    exact sem_drop_false σ τ ((h σ τ).mp hp)
  · intro h σ τ
    constructor
    · intro hp
      exact absurd hp (h σ τ)
    · intro hd
      exact absurd hd (sem_drop_false σ τ)

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
    simp only [historySemantics_iff_packetSemantics, hpq σ τ]
  · intro hpq σ τ
    simpa only [historySemantics_iff_packetSemantics, true_and] using
      hpq ⟨σ, []⟩ ⟨τ, []⟩

theorem netkatIsZero_history_correct (p : NetKAT) :
    netkatIsZero p = true ↔ ∀ h h' : History, ¬ HistorySemantics p h h' := by
  rw [netkatIsZero, netkatEquiv_history_correct]
  simp only [HistorySemantics, iff_false]

/-- Elaborate the complete-test shorthand into the common NetKAT syntax
    of primitive field tests, sequencing and identity. -/
def completeTestExpr (α : CompleteTest) : NetKAT :=
  NetKAT.fieldEnum.foldr (fun f rest => .seq (NetKAT.fieldTest f (α f)) rest) .id

theorem completeTestExpr_correct (α : CompleteTest) (σ τ : CtxPkt) :
    Semantics (completeTestExpr α) σ τ ↔ Semantics (.completeTest α) σ τ := by
  have fields (fs : List FieldName) :
      Semantics (fs.foldr (fun f rest => .seq (NetKAT.fieldTest f (α f)) rest) .id) σ τ ↔
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
