------------------------------------------------------------------------
-- Executable evaluator for the initial NetKAT fragment
------------------------------------------------------------------------

import DyNetKAT.NetKAT.Semantics
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Multiset.MapFold

namespace DyNetKAT.NetKAT

private def ctxPktDecidableEq : DecidableEq CtxPkt := by
  intro σ τ
  exact decidable_of_iff (∀ f ∈ NetKAT.fieldEnum, σ f = τ f) (by
    constructor
    · intro h
      funext f
      exact h f (NetKAT.fieldEnum_complete f)
    · intro h f hf
      exact congrFun h f)

local instance : DecidableEq CtxPkt := ctxPktDecidableEq

/-- The result of evaluating a NetKAT term.

    `supported` deliberately distinguishes a computed empty output from an
    evaluator that does not yet support a term constructor. -/
inductive EvalResult where
  | supported (outputs : Finset CtxPkt)
  | unsupported

namespace EvalResult

/-- Extract computed outputs, if evaluation was supported. -/
def outputs : EvalResult → Option (Finset CtxPkt)
  | .supported packets => some packets
  | .unsupported => none

end EvalResult

private def combineEvalResult (left right : EvalResult) : EvalResult :=
  match left, right with
  | .supported a, .supported b => .supported (a ∪ b)
  | _, _ => .unsupported

private def evalSeqWith (step : CtxPkt → EvalResult) (packets : Multiset CtxPkt) : EvalResult :=
  let op := fun τ acc => combineEvalResult (step τ) acc
  letI : LeftCommutative op := by
    constructor
    intro a b c
    by_cases ha : step a = .unsupported
    · simp [op, combineEvalResult, ha]
    · obtain ⟨oa, ha⟩ : ∃ oa, step a = .supported oa := by
        cases h : step a with
        | unsupported => exact (ha h).elim
        | supported oa => exact ⟨oa, rfl⟩
      by_cases hb : step b = .unsupported
      · simp [op, combineEvalResult, ha, hb]
      · obtain ⟨ob, hb⟩ : ∃ ob, step b = .supported ob := by
          cases h : step b with
          | unsupported => exact (hb h).elim
          | supported ob => exact ⟨ob, rfl⟩
        cases c with
        | unsupported => simp [op, combineEvalResult, ha, hb]
        | supported oc =>
            simp [op, combineEvalResult, ha, hb, Finset.union_assoc,
              Finset.union_left_comm, Finset.union_comm]
  Multiset.foldr op (.supported ∅) packets

private theorem evalSeqWith_supported
    (step : CtxPkt → EvalResult)
    (hstep : ∀ τ, ∃ A : Finset CtxPkt, step τ = .supported A)
    (packets : Multiset CtxPkt) :
    ∃ B : Finset CtxPkt, evalSeqWith step packets = .supported B := by
  induction packets using Multiset.induction_on with
  | empty =>
      exact ⟨∅, by simp [evalSeqWith]
        ⟩
  | @cons τ packets ih =>
      obtain ⟨A, hA⟩ := hstep τ
      obtain ⟨B, hB⟩ := ih
      let op := fun τ acc => combineEvalResult (step τ) acc
      have : LeftCommutative op := by
        constructor
        intro a b c
        by_cases ha : step a = .unsupported
        · simp [op, combineEvalResult, ha]
        · obtain ⟨oa, ha⟩ : ∃ oa, step a = .supported oa := by
            cases h : step a with
            | unsupported => exact (ha h).elim
            | supported oa => exact ⟨oa, rfl⟩
          by_cases hb : step b = .unsupported
          · simp [op, combineEvalResult, ha, hb]
          · obtain ⟨ob, hb⟩ : ∃ ob, step b = .supported ob := by
              cases h : step b with
              | unsupported => exact (hb h).elim
              | supported ob => exact ⟨ob, rfl⟩
            cases c with
            | unsupported => simp [op, combineEvalResult, ha, hb]
            | supported oc =>
                simp [op, combineEvalResult, ha, hb, Finset.union_assoc,
                  Finset.union_left_comm, Finset.union_comm]
      refine ⟨A ∪ B, ?_⟩
      simp only [evalSeqWith, Multiset.foldr_cons]
      have hB' : Multiset.foldr
          (fun τ acc => combineEvalResult (step τ) acc)
          (.supported ∅) packets = .supported B := by
        simpa [evalSeqWith] using hB
      rw [hA, hB']
      simp [combineEvalResult,
        Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]

private def postWith (step : CtxPkt → EvalResult) (packets : Finset CtxPkt) : EvalResult :=
  evalSeqWith step packets.1

private theorem postWith_supported
    (step : CtxPkt → EvalResult)
    (hstep : ∀ τ, ∃ A : Finset CtxPkt, step τ = .supported A)
    (packets : Finset CtxPkt) :
    ∃ B : Finset CtxPkt, postWith step packets = .supported B := by
  exact evalSeqWith_supported step hstep packets.1

private def boundedStarWith (step : CtxPkt → EvalResult) : Nat → CtxPkt → EvalResult
  | 0, σ => .supported {σ}
  | n + 1, σ =>
      match boundedStarWith step n σ with
      | .unsupported => .unsupported
      | .supported packets =>
          match postWith step packets with
          | .unsupported => .unsupported
           | .supported next => .supported (packets ∪ next)

private theorem boundedStarWith_supported
    (step : CtxPkt → EvalResult)
    (hstep : ∀ τ, ∃ A : Finset CtxPkt, step τ = .supported A) :
    ∀ n σ, ∃ B : Finset CtxPkt,
      boundedStarWith step n σ = .supported B := by
  intro n
  induction n with
  | zero =>
      intro σ
      exact ⟨{σ}, rfl⟩
  | succ n ih =>
      intro σ
      obtain ⟨A, hA⟩ := ih σ
      obtain ⟨B, hB⟩ := postWith_supported step hstep A
      refine ⟨A ∪ B, ?_⟩
      simp [boundedStarWith, hA, hB]

private def evalPredicate : Predicate → CtxPkt → EvalResult
  | .pFalse, _ => .supported ∅
  | .pTrue, σ => .supported {σ}
  | .pFieldEq ⟨f, v⟩, σ =>
      if σ f = v then .supported {σ} else .supported ∅
  | .pAnd p q, σ =>
      match evalPredicate p σ, evalPredicate q σ with
      | .supported A, .supported B =>
          if σ ∈ A ∧ σ ∈ B then .supported {σ} else .supported ∅
      | _, _ => .unsupported
  | .pOr p q, σ =>
      match evalPredicate p σ, evalPredicate q σ with
      | .supported A, .supported B =>
          if σ ∈ A ∨ σ ∈ B then .supported {σ} else .supported ∅
      | _, _ => .unsupported
  | .pNot p, σ =>
      match evalPredicate p σ with
      | .supported A => if σ ∈ A then .supported ∅ else .supported {σ}
      | .unsupported => .unsupported

mutual
  /-- Execute a NetKAT term on an input packet. -/
  def execute : NetKAT → CtxPkt → EvalResult
    | .drop, _ => .supported ∅
    | .id, σ => .supported {σ}
    | .test p, σ => evalPredicate p σ
    | .assign1 f v, σ => .supported {Packet.update σ f v}
    | .union n₁ n₂, σ =>
        match execute n₁ σ, execute n₂ σ with
        | .supported outputs₁, .supported outputs₂ =>
            .supported (outputs₁ ∪ outputs₂)
        | _, _ => .unsupported
    | .seq p q, σ =>
        match execute p σ with
        | .unsupported => .unsupported
         | .supported A => evalSeq q A.1
    | .star p, σ => boundedStarWith (execute p) (Fintype.card CtxPkt) σ
    | .completeTest α, σ =>
        if σ = α then .supported {σ} else .supported ∅

  /-- Evaluate the second operand on each reachable intermediate packet. -/
  def evalSeq : NetKAT → Multiset CtxPkt → EvalResult
    | q, packets =>
        let op := fun τ acc => combineEvalResult (execute q τ) acc
        letI : LeftCommutative op := by
          constructor
          intro a b c
          by_cases ha : execute q a = .unsupported
          · simp [op, combineEvalResult, ha]
          · obtain ⟨oa, ha⟩ : ∃ oa, execute q a = .supported oa := by
              cases h : execute q a with
              | unsupported => exact (ha h).elim
              | supported oa => exact ⟨oa, rfl⟩
            by_cases hb : execute q b = .unsupported
            · simp [op, combineEvalResult, ha, hb]
            · obtain ⟨ob, hb⟩ : ∃ ob, execute q b = .supported ob := by
                cases h : execute q b with
                | unsupported => exact (hb h).elim
                | supported ob => exact ⟨ob, rfl⟩
              cases c with
              | unsupported => simp [op, combineEvalResult, ha, hb]
              | supported oc =>
                  simp [op, combineEvalResult, ha, hb, Finset.union_assoc,
                    Finset.union_left_comm, Finset.union_comm]
        Multiset.foldr op (.supported ∅) packets
end

/-- Evaluate a policy on every packet in a finite reachable set. -/
def post (p : NetKAT) (packets : Finset CtxPkt) : EvalResult :=
  evalSeq p packets.1

private theorem evalSeqWith_execute_eq (q : NetKAT) (packets : Multiset CtxPkt) :
    evalSeqWith (execute q) packets = evalSeq q packets := by
  simp [evalSeqWith, evalSeq]

private theorem postWith_execute_eq (q : NetKAT) (packets : Finset CtxPkt) :
    postWith (execute q) packets = post q packets := by
  simp [postWith, post, evalSeqWith_execute_eq]

/-- Executable reachability through at most a bounded number of policy steps.

    The evaluator keeps `unsupported` distinct from a supported empty set at
    every iteration, so an unsupported required execution is never discarded.
-/
def boundedStar (p : NetKAT) : Nat → CtxPkt → EvalResult
  | 0, σ => .supported {σ}
  | n + 1, σ =>
      match boundedStar p n σ with
      | .unsupported => .unsupported
      | .supported packets =>
          match post p packets with
           | .unsupported => .unsupported
           | .supported next => .supported (packets ∪ next)

set_option maxRecDepth 100000 in
theorem execute_star_eq_boundedStar
    (p : NetKAT) (σ : CtxPkt) :
    execute (.star p) σ =
      boundedStar p (Fintype.card CtxPkt) σ := by
  rw [execute]
  induction Fintype.card CtxPkt generalizing σ with
  | zero => rfl
  | succ n ih =>
      rw [boundedStarWith, boundedStar, ih]
      cases h : boundedStar p n σ with
      | unsupported => simp [h]
      | supported packets =>
          simp only [h]
          rw [postWith_execute_eq]

/-- Zero iterations reach exactly the input packet. -/
theorem boundedStar_zero (p : NetKAT) (σ : CtxPkt) :
    boundedStar p 0 σ = .supported {σ} := by
  rfl

/-- A supported predecessor and supported post-step yield the union recurrence. -/
theorem boundedStar_succ_supported
    (p : NetKAT) (n : Nat) (σ : CtxPkt)
    (A B : Finset CtxPkt)
    (hA : boundedStar p n σ = .supported A)
    (hB : post p A = .supported B) :
    boundedStar p (n + 1) σ = .supported (A ∪ B) := by
  simp [boundedStar, hA, hB]

/-- An unsupported predecessor propagates through the next bounded iteration. -/
theorem boundedStar_succ_unsupported_previous
    (p : NetKAT) (n : Nat) (σ : CtxPkt)
    (hA : boundedStar p n σ = .unsupported) :
    boundedStar p (n + 1) σ = .unsupported := by
  simp [boundedStar, hA]

/-- An unsupported post-step propagates through the next bounded iteration. -/
theorem boundedStar_succ_unsupported_post
    (p : NetKAT) (n : Nat) (σ : CtxPkt)
    (A : Finset CtxPkt)
    (hA : boundedStar p n σ = .supported A)
    (hB : post p A = .unsupported) :
    boundedStar p (n + 1) σ = .unsupported := by
  simp [boundedStar, hA, hB]

/-- Supported reachable sets are monotone from one bounded iteration to the next. -/
theorem boundedStar_monotone
    (p : NetKAT) (n : Nat) (σ : CtxPkt)
    (A B : Finset CtxPkt)
    (hA : boundedStar p n σ = .supported A)
    (hB : boundedStar p (n + 1) σ = .supported B) :
    A ⊆ B := by
  rw [boundedStar] at hB
  rw [hA] at hB
  cases hpost : post p A with
  | unsupported => simp [hpost] at hB
  | supported C =>
      simp [hpost] at hB
      rw [← hB]
      exact Finset.subset_union_left

/-- Executing `drop` computes the empty output, rather than unsupported. -/
theorem execute_drop (σ : CtxPkt) :
    execute .drop σ = .supported ∅ := by
  simp [execute]

/-- Executing `id` computes the singleton containing its input packet. -/
theorem execute_id (σ : CtxPkt) :
    execute .id σ = .supported {σ} := by
  simp [execute]

/-- Executing a primitive assignment computes its updated packet. -/
theorem execute_assign1 (f : FieldName) (v : FieldValueEnum) (σ : CtxPkt) :
    execute (.assign1 f v) σ = .supported {Packet.update σ f v} := by
  simp [execute]

/-- Executing a complete test keeps a matching packet and rejects a nonmatching
    packet with a supported empty result. -/
theorem execute_completeTest (α : CompleteTest) (σ : CtxPkt) :
    execute (.completeTest α) σ =
      if σ = α then .supported {σ} else .supported ∅ := by
  simp [execute]

/-- Executing a matching primitive field-equality test keeps its input packet. -/
theorem execute_fieldTest_match (f : FieldName) (v : FieldValueEnum) (σ : CtxPkt)
    (h : σ f = v) :
    execute (NetKAT.fieldTest f v) σ = .supported {σ} := by
  simp [execute, evalPredicate, NetKAT.fieldTest, h]

/-- Executing a nonmatching primitive field-equality test produces no packets. -/
theorem execute_fieldTest_nonmatch (f : FieldName) (v : FieldValueEnum) (σ : CtxPkt)
    (h : σ f ≠ v) :
    execute (NetKAT.fieldTest f v) σ = .supported ∅ := by
  simp [execute, evalPredicate, NetKAT.fieldTest, h]

/-- Executing a union of two supported terms unions their computed outputs. -/
theorem execute_union_supported (n₁ n₂ : NetKAT) (σ : CtxPkt)
    (outputs₁ outputs₂ : Finset CtxPkt)
    (h₁ : execute n₁ σ = .supported outputs₁)
    (h₂ : execute n₂ σ = .supported outputs₂) :
    execute (.union n₁ n₂) σ = .supported (outputs₁ ∪ outputs₂) := by
  simp [execute, h₁, h₂]

/-- An unsupported left operand makes union evaluation unsupported. -/
theorem execute_union_unsupported_left (n₁ n₂ : NetKAT) (σ : CtxPkt)
    (h₁ : execute n₁ σ = .unsupported) :
    execute (.union n₁ n₂) σ = .unsupported := by
  simp [execute, h₁]

/-- An unsupported right operand makes union evaluation unsupported. -/
theorem execute_union_unsupported_right (n₁ n₂ : NetKAT) (σ : CtxPkt)
    (h₂ : execute n₂ σ = .unsupported) :
    execute (.union n₁ n₂) σ = .unsupported := by
  simp [execute, h₂]

/-- Sequential execution exposes the finite second-stage fold after the first
    operand has produced a supported intermediate set. -/
theorem execute_seq_supported (p q : NetKAT) (σ : CtxPkt)
    (A : Finset CtxPkt)
    (h₁ : execute p σ = .supported A) :
    execute (.seq p q) σ = evalSeq q A.1 := by
  simp [execute, h₁]

/-- An unsupported first operand propagates through sequential composition. -/
theorem execute_seq_unsupported_left (p q : NetKAT) (σ : CtxPkt)
    (h₁ : execute p σ = .unsupported) :
    execute (.seq p q) σ = .unsupported := by
  simp [execute, h₁]

/-- The empty intermediate set is a supported empty result; the second operand
    is not evaluated. -/
theorem execute_seq_empty (p q : NetKAT) (σ : CtxPkt)
    (h₁ : execute p σ = .supported (∅ : Finset CtxPkt)) :
    execute (.seq p q) σ = .supported ∅ := by
  rw [execute_seq_supported p q σ ∅ h₁]
  simp [evalSeq]

/-- A required unsupported second-stage evaluation propagates.  The hypothesis
    is phrased directly in terms of the executable fold, avoiding any claim
    about unreachable packets. -/
theorem execute_seq_unsupported_right (p q : NetKAT) (σ : CtxPkt)
    (A : Finset CtxPkt)
    (h₁ : execute p σ = .supported A)
    (h₂ : evalSeq q A.1 = .unsupported) :
    execute (.seq p q) σ = .unsupported := by
  rw [execute_seq_supported p q σ A h₁]
  exact h₂

/-- Compositional correctness for a supported sequential evaluation.  The
    executable first-stage result is `A`; `B` is the result of evaluating the
    second stage over exactly those reachable packets. -/
theorem execute_seq_correct
    (p q : NetKAT) (σ r : CtxPkt)
    (A B : Finset CtxPkt)
    (h₁ : execute p σ = .supported A)
    (h₂ : evalSeq q A.1 = .supported B)
    (corr₁ : ∀ τ, Semantics p σ τ ↔ τ ∈ A)
    (corr₂ : ∀ τ, τ ∈ A → ∀ r, Semantics q τ r ↔ r ∈ B)
    (hB : ∀ r, r ∈ B ↔ ∃ τ, τ ∈ A ∧ Semantics q τ r) :
    Semantics (.seq p q) σ r ↔
      r ∈ (match execute (.seq p q) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  rw [execute_seq_supported p q σ A h₁, h₂]
  rw [seq_sem]
  constructor
  · rintro ⟨τ, hp, hq⟩
    have hmem : r ∈ B := (corr₂ τ ((corr₁ τ).mp hp) r).mp hq
    exact hmem
  · intro hr
    obtain ⟨τ, hp, hq⟩ := (hB r).mp hr
    exact ⟨τ, (corr₁ τ).mpr hp, hq⟩

/-- The executable `drop` result has exactly the denotational outputs. -/
theorem execute_drop_correct (σ q : CtxPkt) :
    Semantics .drop σ q ↔
      q ∈ (match execute .drop σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  simp [execute, Semantics]

/-- The executable `id` result has exactly the denotational outputs. -/
theorem execute_id_correct (σ q : CtxPkt) :
    Semantics .id σ q ↔
      q ∈ (match execute .id σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  simp [execute, Semantics, eq_comm]

/-- The executable primitive-assignment result has exactly the denotational
    assignment outputs, in both directions. -/
theorem execute_assign1_correct (f : FieldName) (v : FieldValueEnum)
    (σ q : CtxPkt) :
    Semantics (.assign1 f v) σ q ↔
      q ∈ (match execute (.assign1 f v) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  simp [execute, Semantics]

/-- The executable complete-test result agrees exactly with its relational
    semantics, for both matching and nonmatching packets. -/
theorem execute_completeTest_correct (α : CompleteTest) (σ q : CtxPkt) :
    Semantics (.completeTest α) σ q ↔
      q ∈ (match execute (.completeTest α) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  rw [execute_completeTest]
  by_cases h : σ = α
  · subst h
    simp [Semantics, holdsComplete_iff_eq, eq_comm]
  · simp [Semantics, holdsComplete_iff_eq, h]

/-- The executable primitive field-equality result has exactly the denotational
    test outputs, in both directions. -/
theorem execute_fieldTest_correct (f : FieldName) (v : FieldValueEnum)
    (σ q : CtxPkt) :
    Semantics (NetKAT.fieldTest f v) σ q ↔
      q ∈ (match execute (NetKAT.fieldTest f v) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  rw [fieldTest_sem]
  by_cases h : σ f = v
  · simp [execute, evalPredicate, NetKAT.fieldTest, h]
  · simp [execute, evalPredicate, NetKAT.fieldTest, h]

/-- The executable false-predicate result has exactly the empty denotational
    relation. -/
theorem execute_pFalse_correct (σ q : CtxPkt) :
    Semantics (.test Predicate.pFalse) σ q ↔
      q ∈ (match execute (.test Predicate.pFalse) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  simp [execute, evalPredicate, Semantics, Predicate.holds, Predicate.eval]

/-- Executing the true predicate computes the singleton containing its input. -/
theorem execute_pTrue (σ : CtxPkt) :
    execute (.test Predicate.pTrue) σ = .supported {σ} := by
  simp [execute, evalPredicate]

/-- The executable true-predicate result has exactly the identity relation. -/
theorem execute_pTrue_correct (σ q : CtxPkt) :
    Semantics (.test Predicate.pTrue) σ q ↔
      q ∈ (match execute (.test Predicate.pTrue) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  simp [execute, evalPredicate, Semantics, Predicate.holds, Predicate.eval, eq_comm]

/-- A conjunction of supported component evaluations keeps the input packet
    exactly when both component outputs contain it. -/
theorem execute_pAnd_supported
    (a b : Predicate) (σ : CtxPkt) (A B : Finset CtxPkt)
    (h₁ : execute (.test a) σ = .supported A)
    (h₂ : execute (.test b) σ = .supported B) :
    execute (.test (.pAnd a b)) σ =
      if σ ∈ A ∧ σ ∈ B then .supported {σ} else .supported ∅ := by
  have h₁' : evalPredicate a σ = .supported A := by
    simpa [execute] using h₁
  have h₂' : evalPredicate b σ = .supported B := by
    simpa [execute] using h₂
  simp [execute, evalPredicate, h₁', h₂']

/-- A supported conjunction is semantically correct when both component
    executions are supported and semantically correct. -/
theorem execute_pAnd_correct
    (a b : Predicate) (σ q : CtxPkt) (A B : Finset CtxPkt)
    (h₁ : execute (.test a) σ = .supported A)
    (h₂ : execute (.test b) σ = .supported B)
    (corr₁ : ∀ r, Semantics (.test a) σ r ↔ r ∈ A)
    (corr₂ : ∀ r, Semantics (.test b) σ r ↔ r ∈ B) :
    Semantics (.test (.pAnd a b)) σ q ↔
      q ∈ (match execute (.test (.pAnd a b)) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  rw [andTest_sem, execute_pAnd_supported a b σ A B h₁ h₂]
  by_cases ha : σ ∈ A
  · by_cases hb : σ ∈ B
    · have hpa : a.holds σ := ((corr₁ σ).mpr ha).1
      have hpb : b.holds σ := ((corr₂ σ).mpr hb).1
      simp [ha, hb, hpa, hpb]
    · have : ¬b.holds σ := by
        intro hpb
        exact hb ((corr₂ σ).mp (by simp [Semantics, hpb]))
      simp [ha, hb, this]
  · have : ¬a.holds σ := by
      intro hpa
      exact ha ((corr₁ σ).mp (by simp [Semantics, hpa]))
    simp [ha, this]

/-- A disjunction of supported component evaluations keeps the input packet
    exactly when either component output contains it. -/
theorem execute_pOr_supported
    (a b : Predicate) (σ : CtxPkt) (A B : Finset CtxPkt)
    (h₁ : execute (.test a) σ = .supported A)
    (h₂ : execute (.test b) σ = .supported B) :
    execute (.test (.pOr a b)) σ =
      if σ ∈ A ∨ σ ∈ B then .supported {σ} else .supported ∅ := by
  have h₁' : evalPredicate a σ = .supported A := by
    simpa [execute] using h₁
  have h₂' : evalPredicate b σ = .supported B := by
    simpa [execute] using h₂
  simp [execute, evalPredicate, h₁', h₂']

/-- A supported disjunction is semantically correct when both component
    executions are supported and semantically correct. -/
theorem execute_pOr_correct
    (a b : Predicate) (σ q : CtxPkt) (A B : Finset CtxPkt)
    (h₁ : execute (.test a) σ = .supported A)
    (h₂ : execute (.test b) σ = .supported B)
    (corr₁ : ∀ r, Semantics (.test a) σ r ↔ r ∈ A)
    (corr₂ : ∀ r, Semantics (.test b) σ r ↔ r ∈ B) :
    Semantics (.test (.pOr a b)) σ q ↔
      q ∈ (match execute (.test (.pOr a b)) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  rw [orTest_sem, execute_pOr_supported a b σ A B h₁ h₂]
  constructor
  · rintro ⟨hab, hqσ⟩
    have hmem : q ∈ A ∨ q ∈ B := by
      rcases hab with ha | hb
      · exact Or.inl ((corr₁ q).mp (by simp [Semantics, ha, hqσ]))
      · exact Or.inr ((corr₂ q).mp (by simp [Semantics, hb, hqσ]))
    have hmemσ : σ ∈ A ∨ σ ∈ B := by simpa [hqσ] using hmem
    rw [hqσ]
    simp only [EvalResult.supported.injEq] at hmemσ
    simpa [hmemσ]
  · intro hq
    by_cases hmem : σ ∈ A ∨ σ ∈ B
    · have hqeq : q = σ := by simpa [hmem] using hq
      subst q
      have hholds : a.holds σ ∨ b.holds σ :=
        hmem.elim (fun ha => Or.inl (((corr₁ σ).mpr ha).1))
          (fun hb => Or.inr (((corr₂ σ).mpr hb).1))
      exact ⟨hholds, rfl⟩
    · simp [hmem] at hq

/- A supported negation keeps the input packet exactly when its component
   output does not contain that packet. -/
theorem execute_pNot_supported
    (a : Predicate) (σ : CtxPkt) (A : Finset CtxPkt)
    (h : execute (.test a) σ = .supported A) :
    execute (.test (.pNot a)) σ =
      if σ ∈ A then .supported ∅ else .supported {σ} := by
  have h' : evalPredicate a σ = .supported A := by
    simpa [execute] using h
  simp [execute, evalPredicate, h']

/-- Every predicate test evaluates to a supported finite output set. -/
theorem execute_test_supported
    (a : Predicate) (σ : CtxPkt) :
    ∃ A : Finset CtxPkt,
      execute (.test a) σ = .supported A := by
  induction a generalizing σ with
  | pFalse => exact ⟨∅, by simp [execute, evalPredicate]⟩
  | pTrue => exact ⟨{σ}, by simp [execute, evalPredicate]⟩
  | pFieldEq fe =>
      by_cases h : σ fe.field = fe.value
      · exact ⟨{σ}, by simp [execute, evalPredicate, h]⟩
      · exact ⟨∅, by simp [execute, evalPredicate, h]⟩
  | pAnd p q ihp ihq =>
      obtain ⟨A, hA⟩ := ihp σ
      obtain ⟨B, hB⟩ := ihq σ
      rw [execute_pAnd_supported p q σ A B hA hB]
      split <;> simp_all
  | pOr p q ihp ihq =>
      obtain ⟨A, hA⟩ := ihp σ
      obtain ⟨B, hB⟩ := ihq σ
      rw [execute_pOr_supported p q σ A B hA hB]
      split <;> simp_all
  | pNot p ih =>
      obtain ⟨A, hA⟩ := ih σ
      rw [execute_pNot_supported p σ A hA]
      split <;> simp_all

/- Every NetKAT policy evaluates to a finite supported output set. -/
theorem execute_supported
    (p : NetKAT) (σ : CtxPkt) :
    ∃ B : Finset CtxPkt,
      execute p σ = .supported B := by
  induction p generalizing σ with
  | drop =>
      exact ⟨∅, by simp [execute]
        ⟩
  | id =>
      exact ⟨{σ}, by simp [execute]
        ⟩
  | test a =>
      exact execute_test_supported a σ
  | completeTest α =>
      by_cases h : σ = α
      · exact ⟨{σ}, by simp [execute, h]
          ⟩
      · exact ⟨∅, by simp [execute, h]
          ⟩
  | assign1 f v =>
      exact ⟨{Packet.update σ f v}, by simp [execute]
        ⟩
  | union p q ihp ihq =>
      obtain ⟨A, hA⟩ := ihp σ
      obtain ⟨B, hB⟩ := ihq σ
      exact ⟨A ∪ B, by simp [execute, hA, hB]
        ⟩
  | seq p q ihp ihq =>
      obtain ⟨A, hA⟩ := ihp σ
      obtain ⟨B, hB⟩ := evalSeqWith_supported (fun τ => execute q τ)
        (fun τ => ihq τ) A.1
      refine ⟨B, ?_⟩
      rw [execute, hA]
      simpa [evalSeqWith_execute_eq] using hB
  | star p ihp =>
      obtain ⟨B, hB⟩ := boundedStarWith_supported (execute p)
        (fun τ => ihp τ)
        (Fintype.card CtxPkt) σ
      exact ⟨B, by
        change execute (.star p) σ = .supported B
        simpa [execute] using hB⟩

/- A supported, semantically correct predicate negation agrees with the
   relational negation semantics. -/
theorem execute_pNot_correct
    (a : Predicate) (σ q : CtxPkt) (A : Finset CtxPkt)
    (h : execute (.test a) σ = .supported A)
    (corr : ∀ r, Semantics (.test a) σ r ↔ r ∈ A) :
    Semantics (.test (.pNot a)) σ q ↔
      q ∈ (match execute (.test (.pNot a)) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  rw [notTest_sem, execute_pNot_supported a σ A h]
  by_cases hA : σ ∈ A
  · have ha : a.holds σ := (corr σ).mpr hA |>.1
    simp [hA, ha]
  · have ha : ¬a.holds σ := by
      intro ha
      exact hA ((corr σ).mp (by simp [Semantics, ha]))
    simp [hA, ha]

/- Every predicate test is supported and its finite output set is exactly the
   relational test relation. -/
theorem execute_test_correct
    (a : Predicate) (σ : CtxPkt) :
    ∃ A : Finset CtxPkt,
      execute (.test a) σ = .supported A ∧
      ∀ q, Semantics (.test a) σ q ↔ q ∈ A := by
  induction a generalizing σ with
  | pFalse =>
      refine ⟨∅, by simp [execute, evalPredicate], ?_⟩
      intro q
      simpa [execute, evalPredicate, Semantics, Predicate.holds, Predicate.eval]
  | pTrue =>
      refine ⟨{σ}, by simp [execute, evalPredicate], ?_⟩
      intro q
      simpa [execute, evalPredicate, Semantics, Predicate.holds, Predicate.eval,
        eq_comm]
  | pFieldEq fe =>
      by_cases h : σ fe.field = fe.value
      · refine ⟨{σ}, by simp [execute, evalPredicate, h], ?_⟩
        intro q
        simpa [NetKAT.fieldTest, execute, evalPredicate, Semantics,
          Predicate.holds, Predicate.eval, h, eq_comm]
      · refine ⟨∅, by simp [execute, evalPredicate, h], ?_⟩
        intro q
        simpa [NetKAT.fieldTest, execute, evalPredicate, Semantics,
          Predicate.holds, Predicate.eval, h]
  | pAnd a b iha ihb =>
      obtain ⟨A, hA, corrA⟩ := iha σ
      obtain ⟨B, hB, corrB⟩ := ihb σ
      obtain ⟨C, hC⟩ := execute_test_supported (.pAnd a b) σ
      refine ⟨C, hC, ?_⟩
      intro q
      simpa [hC] using
        (execute_pAnd_correct a b σ q A B hA hB corrA corrB)
  | pOr a b iha ihb =>
      obtain ⟨A, hA, corrA⟩ := iha σ
      obtain ⟨B, hB, corrB⟩ := ihb σ
      obtain ⟨C, hC⟩ := execute_test_supported (.pOr a b) σ
      refine ⟨C, hC, ?_⟩
      intro q
      simpa [hC] using
        (execute_pOr_correct a b σ q A B hA hB corrA corrB)
  | pNot a iha =>
      obtain ⟨A, hA, corrA⟩ := iha σ
      obtain ⟨C, hC⟩ := execute_test_supported (.pNot a) σ
      refine ⟨C, hC, ?_⟩
      intro q
      simpa [hC] using
        (execute_pNot_correct a σ q A hA corrA)

/-- A supported union result exactly matches the denotational union semantics
    when both supported operand results do. -/
theorem execute_union_correct (n₁ n₂ : NetKAT) (σ q : CtxPkt)
    (outputs₁ outputs₂ : Finset CtxPkt)
    (h₁ : execute n₁ σ = .supported outputs₁)
    (h₂ : execute n₂ σ = .supported outputs₂)
    (corr₁ : ∀ q, Semantics n₁ σ q ↔ q ∈ outputs₁)
    (corr₂ : ∀ q, Semantics n₂ σ q ↔ q ∈ outputs₂) :
    Semantics (.union n₁ n₂) σ q ↔
      q ∈ (match execute (.union n₁ n₂) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  rw [execute_union_supported n₁ n₂ σ outputs₁ outputs₂ h₁ h₂]
  rw [union_sem]
  simp only [Finset.mem_union]
  exact or_congr (corr₁ q) (corr₂ q)

/-- A supported `post` result is exactly one-step relational reachability when
    every input packet has a supported, semantically correct execution. -/
theorem post_correct
    (p : NetKAT) (A B : Finset CtxPkt)
    (hpost : post p A = .supported B)
    (hEval : ∀ σ, σ ∈ A → ∃ outputs,
      execute p σ = .supported outputs ∧
        ∀ τ, Semantics p σ τ ↔ τ ∈ outputs) :
    ∀ τ, τ ∈ B ↔ ∃ σ, σ ∈ A ∧ Semantics p σ τ := by
  have hfold : ∀ packets : Multiset CtxPkt,
      (∀ σ, σ ∈ packets → ∃ outputs,
        execute p σ = .supported outputs ∧
          ∀ τ, Semantics p σ τ ↔ τ ∈ outputs) →
      ∃ outputs, evalSeq p packets = .supported outputs ∧
        ∀ τ, τ ∈ outputs ↔ ∃ σ, σ ∈ packets ∧ Semantics p σ τ := by
    intro packets
    induction packets using Multiset.induction_on with
    | empty =>
        intro _
        exact ⟨∅, by simp [evalSeq], by simp⟩
    | @cons σ packets ih =>
        intro hpackets
        obtain ⟨outputsσ, hσ, corrσ⟩ := hpackets σ (by simp)
        obtain ⟨outputs, houtputs, corr⟩ := ih (by
          intro τ hτ
          exact hpackets τ (by simp [hτ]))
        refine ⟨outputsσ ∪ outputs, ?_, ?_⟩
        · unfold evalSeq
          rw [Multiset.foldr_cons, hσ]
          simp only [evalSeq] at houtputs
          rw [houtputs]
          rfl
        · intro τ
          simp only [Finset.mem_union]
          constructor
          · intro hτ
            rcases hτ with hτ | hτ
            · exact ⟨σ, by simp, (corrσ τ).mpr hτ⟩
            · obtain ⟨ρ, hρ, hsem⟩ := (corr τ).mp hτ
              exact ⟨ρ, by simp [hρ], hsem⟩
          · rintro ⟨ρ, hρ, hsem⟩
            rcases (by simpa using hρ : ρ = σ ∨ ρ ∈ packets) with rfl | hρ
            · exact Or.inl ((corrσ τ).mp hsem)
            · exact Or.inr ((corr τ).mpr ⟨ρ, hρ, hsem⟩)
  intro τ
  rw [post] at hpost
  obtain ⟨outputs, houtputs, hcorr⟩ := hfold A.1 (by
    intro σ hσ
    exact hEval σ (by simpa using hσ))
  have hAB : B = outputs := by
    exact EvalResult.supported.inj (hpost.symm.trans houtputs)
  subst hAB
  exact hcorr τ

/-- Relational reachability using at most `n` applications of `p`. -/
def ReachableWithin (p : NetKAT) : Nat → CtxPkt → CtxPkt → Prop
  | 0, σ, τ => τ = σ
  | n + 1, σ, τ =>
      ReachableWithin p n σ τ ∨
        ∃ ρ, ReachableWithin p n σ ρ ∧ Semantics p ρ τ

/-- Zero iterations reach exactly the input packet. -/
theorem reachableWithin_zero_iff (p : NetKAT) (σ τ : CtxPkt) :
    ReachableWithin p 0 σ τ ↔ τ = σ := by
  rfl

/-- One more bounded iteration either keeps a packet already reachable, or
    takes one policy step from a packet reachable at the smaller bound. -/
theorem reachableWithin_succ_iff (p : NetKAT) (n : Nat) (σ τ : CtxPkt) :
    ReachableWithin p (n + 1) σ τ ↔
      ReachableWithin p n σ τ ∨
        ∃ ρ, ReachableWithin p n σ ρ ∧ Semantics p ρ τ := by
  rfl

private theorem reachableWithin_weaken
    (p : NetKAT) {n k : Nat} (h : n ≤ k) {σ τ : CtxPkt} :
    ReachableWithin p n σ τ → ReachableWithin p k σ τ := by
  intro hreach
  induction h with
  | refl => exact hreach
  | @step k h ih => exact Or.inl ih

private theorem reachableWithin_prepend
    (p : NetKAT) {n : Nat} {σ ρ τ : CtxPkt} :
    Semantics p σ ρ → ReachableWithin p n ρ τ →
      ReachableWithin p (n + 1) σ τ := by
  induction n generalizing σ ρ τ with
  | zero =>
      intro hstep hreach
      rw [reachableWithin_zero_iff] at hreach
      subst τ
      rw [reachableWithin_succ_iff]
      exact Or.inr ⟨σ, rfl, hstep⟩
  | succ n ih =>
      intro hstep hreach
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, reachableWithin_succ_iff]
      cases hreach with
      | inl hreach => exact Or.inl (ih hstep hreach)
      | inr hreach =>
          obtain ⟨μ, hμ, hμτ⟩ := hreach
          exact Or.inr ⟨μ, ih hstep hμ, hμτ⟩

private theorem starClosure_append
    {α : Type} {R : α → α → Prop} {a b c : α} :
    StarClosure R a b → R b c → StarClosure R a c := by
  intro hclosure hstep
  induction hclosure with
  | refl => exact StarClosure.step hstep (StarClosure.refl c)
  | @step a b d hab hclosure ih => exact StarClosure.step hab (ih hstep)

private theorem starClosure_iff_reachableWithin
    (p : NetKAT) (σ τ : CtxPkt) :
    StarClosure (Semantics p) σ τ ↔
      ∃ n : Nat, ReachableWithin p n σ τ := by
  constructor
  · intro hclosure
    induction hclosure with
    | refl => exact ⟨0, rfl⟩
    | @step a b c hab hclosure ih =>
        obtain ⟨n, hreach⟩ := ih
        exact ⟨n + 1, reachableWithin_prepend p hab hreach⟩
  · rintro ⟨n, hreach⟩
    induction n generalizing σ τ with
    | zero =>
        rw [reachableWithin_zero_iff] at hreach
        subst τ
        exact StarClosure.refl σ
    | succ n ih =>
        rw [reachableWithin_succ_iff] at hreach
        cases hreach with
        | inl hreach => exact ih σ τ hreach
        | inr hreach =>
            obtain ⟨ρ, hρ, hρτ⟩ := hreach
            exact starClosure_append (ih σ ρ hρ) hρτ

theorem semantics_star_iff_reachableWithin
    (p : NetKAT) (σ τ : CtxPkt) :
    Semantics (.star p) σ τ ↔
      ∃ n : Nat, ReachableWithin p n σ τ := by
  exact starClosure_iff_reachableWithin p σ τ

 /-- Once one bounded reachability step adds no packets, the next step adds no
    packets either. -/
theorem reachableWithin_stable_succ
    (p : NetKAT) (n : Nat) (σ : CtxPkt)
    (hstable : ∀ τ, ReachableWithin p (n + 1) σ τ ↔
      ReachableWithin p n σ τ) :
    ∀ τ, ReachableWithin p (n + 2) σ τ ↔
      ReachableWithin p (n + 1) σ τ := by
  intro τ
  rw [reachableWithin_succ_iff]
  constructor
  · intro hreach
    cases hreach with
    | inl hreach => exact hreach
    | inr hstep =>
        obtain ⟨ρ, hρ, hρτ⟩ := hstep
        rw [reachableWithin_succ_iff]
        exact Or.inr ⟨ρ, (hstable ρ).mp hρ, hρτ⟩
  · intro hreach
    exact reachableWithin_weaken p (Nat.le_succ (n + 1)) hreach

private theorem reachableWithin_stable_of_le
    (p : NetKAT) (n k : Nat) (σ : CtxPkt)
    (hstable : ∀ τ, ReachableWithin p (n + 1) σ τ ↔
      ReachableWithin p n σ τ) (h : n ≤ k) :
    ∀ τ, ReachableWithin p (k + 1) σ τ ↔
      ReachableWithin p k σ τ := by
  induction h with
  | refl => exact hstable
  | @step k h ih =>
      exact reachableWithin_stable_succ p k σ ih

/- A finite chain of reachable packets must have an adjacent stable pair. -/
set_option maxRecDepth 100000 in
theorem reachableWithin_finite_stabilizes
    (p : NetKAT) (σ : CtxPkt) :
    ∃ n, n ≤ Fintype.card CtxPkt ∧
      ∀ τ, ReachableWithin p (n + 1) σ τ ↔
        ReachableWithin p n σ τ := by
  classical
  let reached : Nat → Finset CtxPkt := fun n =>
    Finset.univ.filter (ReachableWithin p n σ)
  have hsubset : ∀ n, reached n ⊆ reached (n + 1) := by
    intro n τ hτ
    rw [Finset.mem_filter] at hτ ⊢
    exact ⟨Finset.mem_univ _, reachableWithin_weaken p (Nat.le_succ n) hτ.2⟩
  by_cases hex : ∃ n, n ≤ Fintype.card CtxPkt ∧
      ∀ τ, ReachableWithin p (n + 1) σ τ ↔ ReachableWithin p n σ τ
  · exact hex
  · have hnone : ∀ n, n ≤ Fintype.card CtxPkt →
        ¬ (∀ τ, ReachableWithin p (n + 1) σ τ ↔ ReachableWithin p n σ τ) := by
      intro n hn hstable
      exact hex ⟨n, hn, hstable⟩
    have hcard_lower : ∀ k, k ≤ Fintype.card CtxPkt →
        k + 1 ≤ (reached k).card := by
      intro k hk
      induction k with
      | zero =>
          have hσ : σ ∈ reached 0 := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, rfl⟩
          simpa using (Finset.card_pos.mpr ⟨σ, hσ⟩)
      | succ k ih =>
          have hk' : k ≤ Fintype.card CtxPkt := Nat.le_trans (Nat.le_succ k) hk
          have hne : reached k ≠ reached (k + 1) := by
            intro heq
            apply hnone k hk'
            intro τ
            constructor
            · intro hτ
              have hmem : τ ∈ reached (k + 1) := by
                rw [Finset.mem_filter]
                exact ⟨Finset.mem_univ _, hτ⟩
              have hmem' : τ ∈ reached k := heq ▸ hmem
              exact (Finset.mem_filter.mp hmem').2
            · intro hτ
              exact reachableWithin_weaken p (Nat.le_succ k) hτ
          have hlt : (reached k).card < (reached (k + 1)).card := by
            exact Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).2
              ⟨hsubset k, hne⟩)
          omega
    have hlower := hcard_lower (Fintype.card CtxPkt) le_rfl
    have hupper := Finset.card_le_univ (reached (Fintype.card CtxPkt))
    omega

theorem reachableWithin_stable_at_card
    (p : NetKAT) (σ : CtxPkt) :
    ∀ τ,
      ReachableWithin p
        (Fintype.card CtxPkt + 1) σ τ ↔
      ReachableWithin p
        (Fintype.card CtxPkt) σ τ := by
  obtain ⟨n, hn, hstable⟩ := reachableWithin_finite_stabilizes p σ
  exact reachableWithin_stable_of_le p n (Fintype.card CtxPkt) σ hstable hn

private theorem reachableWithin_stable_back
    (p : NetKAT) (n k : Nat) (σ : CtxPkt)
    (hstable : ∀ τ, ReachableWithin p (n + 1) σ τ ↔
      ReachableWithin p n σ τ) (h : n ≤ k) :
    ∀ τ, ReachableWithin p k σ τ → ReachableWithin p n σ τ := by
  induction h with
  | refl => exact fun τ hreach => hreach
  | @step k h ih =>
      intro τ hreach
      have hadj := reachableWithin_stable_of_le p n k σ hstable h
      exact ih τ ((hadj τ).mp hreach)

set_option maxRecDepth 100000 in
theorem reachableWithin_iff_at_card
    (p : NetKAT) (σ τ : CtxPkt) :
    (∃ n : Nat, ReachableWithin p n σ τ) ↔
      ReachableWithin p (Fintype.card CtxPkt) σ τ := by
  constructor
  · rintro ⟨n, hreach⟩
    by_cases hle : n ≤ Fintype.card CtxPkt
    · exact reachableWithin_weaken p hle hreach
    · have hcard : Fintype.card CtxPkt ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hle)
      have hstable := reachableWithin_stable_at_card p σ
      exact reachableWithin_stable_back p (Fintype.card CtxPkt) n σ hstable hcard τ hreach
  · intro hreach
    exact ⟨Fintype.card CtxPkt, hreach⟩

/-- A supported bounded computation denotes exactly its relationally reachable
    packets, provided every packet reached at the bound is supported and
    semantically correct for one further policy evaluation. -/
theorem boundedStar_correct
    (p : NetKAT) (n : Nat) (σ : CtxPkt) (B : Finset CtxPkt)
    (hbound : boundedStar p n σ = .supported B)
    (hEval : ∀ ρ, ReachableWithin p n σ ρ → ∃ outputs,
      execute p ρ = .supported outputs ∧
        ∀ τ, Semantics p ρ τ ↔ τ ∈ outputs) :
    ∀ τ, τ ∈ B ↔ ReachableWithin p n σ τ := by
  induction n generalizing σ B with
  | zero =>
      intro τ
      rw [boundedStar_zero] at hbound
      have hB : B = {σ} := EvalResult.supported.inj hbound.symm
      subst hB
      exact (Finset.mem_singleton.trans
        (reachableWithin_zero_iff p σ τ).symm)
  | succ n ih =>
      cases hA : boundedStar p n σ with
      | unsupported =>
          rw [boundedStar, hA] at hbound
          contradiction
      | supported A =>
          cases hC : post p A with
          | unsupported =>
              simp [boundedStar, hA, hC] at hbound
          | supported C =>
              have hEvalA : ∀ ρ, ReachableWithin p n σ ρ → ∃ outputs,
                  execute p ρ = .supported outputs ∧
                    ∀ τ, Semantics p ρ τ ↔ τ ∈ outputs := by
                intro ρ hρ
                exact hEval ρ (reachableWithin_weaken p (Nat.le_succ n) hρ)
              have hIH : ∀ τ, τ ∈ A ↔ ReachableWithin p n σ τ :=
                ih σ A hA hEvalA
              have hpostCorrect : ∀ τ, τ ∈ C ↔
                  ∃ ρ, ρ ∈ A ∧ Semantics p ρ τ :=
                post_correct p A C hC (by
                  intro ρ hρ
                  exact hEvalA ρ (hIH ρ |>.mp hρ))
              intro τ
              have hBC : B = A ∪ C := by
                apply EvalResult.supported.inj
                simpa [boundedStar, hA, hC] using hbound.symm
              subst hBC
              rw [reachableWithin_succ_iff]
              simp only [Finset.mem_union, hIH, hpostCorrect]

theorem execute_star_correct
    (p : NetKAT) (σ : CtxPkt) (B : Finset CtxPkt)
    (hExec : execute (.star p) σ = .supported B)
    (hEval :
      ∀ ρ,
        ReachableWithin p (Fintype.card CtxPkt) σ ρ →
          ∃ outputs,
            execute p ρ = .supported outputs ∧
              ∀ τ, Semantics p ρ τ ↔ τ ∈ outputs) :
    ∀ τ, Semantics (.star p) σ τ ↔ τ ∈ B := by
  have hbound : boundedStar p (Fintype.card CtxPkt) σ = .supported B := by
    rw [← execute_star_eq_boundedStar p σ]
    exact hExec
  have hreach := boundedStar_correct p (Fintype.card CtxPkt) σ B hbound hEval
  intro τ
  rw [semantics_star_iff_reachableWithin, reachableWithin_iff_at_card]
  exact (hreach τ).symm

/-- Every NetKAT policy evaluates to a supported finite set which is exactly its
    relational semantics, without any additional evaluator assumptions. -/
theorem execute_correct
    (p : NetKAT) (σ : CtxPkt) :
    ∃ B : Finset CtxPkt,
      execute p σ = .supported B ∧
      ∀ τ, Semantics p σ τ ↔ τ ∈ B := by
  induction p generalizing σ with
  | drop =>
      have h := execute_drop σ
      refine ⟨∅, h, ?_⟩
      intro τ
      simpa [h] using (execute_drop_correct σ τ)
  | id =>
      have h := execute_id σ
      refine ⟨{σ}, h, ?_⟩
      intro τ
      simpa [h] using (execute_id_correct σ τ)
  | test a =>
      exact execute_test_correct a σ
  | completeTest α =>
      refine ⟨if σ = α then {σ} else ∅, ?_, ?_⟩
      · rw [execute_completeTest]
        split <;> rfl
      · intro τ
        by_cases h : σ = α
        · subst h
          simpa [execute_completeTest] using (execute_completeTest_correct σ σ τ)
        · simpa [execute_completeTest, h] using (execute_completeTest_correct α σ τ)
  | assign1 f v =>
      have h := execute_assign1 f v σ
      refine ⟨{Packet.update σ f v}, h, ?_⟩
      intro τ
      simpa [h] using (execute_assign1_correct f v σ τ)
  | union p q ihp ihq =>
      obtain ⟨A, hA, corrA⟩ := ihp σ
      obtain ⟨B, hB, corrB⟩ := ihq σ
      have h := execute_union_supported p q σ A B hA hB
      refine ⟨A ∪ B, h, ?_⟩
      intro τ
      simpa [h] using (execute_union_correct p q σ τ A B hA hB corrA corrB)
  | seq p q ihp ihq =>
      obtain ⟨A, hA, corrA⟩ := ihp σ
      obtain ⟨B, hB⟩ := evalSeqWith_supported (fun τ => execute q τ)
        (fun τ => (execute_supported q τ)) A.1
      have hB' : evalSeq q A.1 = .supported B := by
        simpa [evalSeqWith_execute_eq] using hB
      have hpost : post q A = .supported B := by
        simpa [post] using hB'
      have hcorrB : ∀ r, r ∈ B ↔ ∃ τ, τ ∈ A ∧ Semantics q τ r := by
        exact post_correct q A B hpost (by
          intro τ hτ
          obtain ⟨C, hC, corrC⟩ := ihq τ
          exact ⟨C, hC, corrC⟩)
      have hseq : execute (.seq p q) σ = .supported B := by
        exact execute_seq_supported p q σ A hA |>.trans hB'
      refine ⟨B, hseq, ?_⟩
      intro r
      rw [seq_sem]
      constructor
      · rintro ⟨τ, hp, hq⟩
        exact (hcorrB r).mpr ⟨τ, (corrA τ).mp hp, hq⟩
      · intro hr
        obtain ⟨τ, hτ, hq⟩ := (hcorrB r).mp hr
        exact ⟨τ, (corrA τ).mpr hτ, hq⟩
  | star p ihp =>
      obtain ⟨B, hB⟩ := execute_supported (.star p) σ
      refine ⟨B, hB, ?_⟩
      intro τ
      exact execute_star_correct p σ B hB (by
        intro ρ _
        exact ihp ρ) τ

end DyNetKAT.NetKAT
