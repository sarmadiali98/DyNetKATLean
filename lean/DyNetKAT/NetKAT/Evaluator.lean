------------------------------------------------------------------------
-- Executable evaluator for the initial NetKAT fragment
------------------------------------------------------------------------

import DyNetKAT.NetKAT.Semantics
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card
import Mathlib.Data.Multiset.MapFold
import Mathlib.Logic.Function.Iterate

namespace DyNetKAT.NetKAT

variable {schema : PacketSchema}

local instance : DecidableEq schema.Packet := schema.packetEq

local instance : Fintype schema.Packet :=
  letI := schema.fieldEq
  letI := schema.fieldFinite
  letI := schema.valueFinite
  inferInstanceAs (Fintype ((f : schema.Field) → schema.Value f))

/-- The result of evaluating a NetKAT term.

    `supported` deliberately distinguishes a computed empty output from an
    evaluator that does not yet support a term constructor. -/
inductive EvalResult (schema : PacketSchema := ctxSchema) where
  | supported (outputs : Finset schema.Packet)
  | unsupported
  deriving DecidableEq

namespace EvalResult

/-- Extract computed outputs, if evaluation was supported. -/
def outputs : EvalResult schema → Option (Finset schema.Packet)
  | .supported packets => some packets
  | .unsupported => none

end EvalResult

private def combineEvalResult (left right : EvalResult schema) : EvalResult schema :=
  match left, right with
  | .supported a, .supported b => .supported (a ∪ b)
  | _, _ => .unsupported

private def evalSeqWith (step : schema.Packet → (EvalResult schema)) (packets : Multiset schema.Packet) : EvalResult schema :=
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
    (step : schema.Packet → (EvalResult schema))
    (hstep : ∀ τ, ∃ A : Finset schema.Packet, step τ = .supported A)
    (packets : Multiset schema.Packet) :
    ∃ B : Finset schema.Packet, evalSeqWith step packets = .supported B := by
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

private def postWith (step : schema.Packet → (EvalResult schema)) (packets : Finset schema.Packet) : EvalResult schema :=
  evalSeqWith step packets.1

private theorem postWith_supported
    (step : schema.Packet → (EvalResult schema))
    (hstep : ∀ τ, ∃ A : Finset schema.Packet, step τ = .supported A)
    (packets : Finset schema.Packet) :
    ∃ B : Finset schema.Packet, postWith step packets = .supported B := by
  exact evalSeqWith_supported step hstep packets.1

private def boundedStarWith (step : schema.Packet → (EvalResult schema)) : Nat → schema.Packet → (EvalResult schema)
  | 0, σ => .supported {σ}
  | n + 1, σ =>
      match boundedStarWith step n σ with
      | .unsupported => .unsupported
      | .supported packets =>
          match postWith step packets with
          | .unsupported => .unsupported
           | .supported next => .supported (packets ∪ next)

private def advanceStar (step : schema.Packet → (EvalResult schema)) : EvalResult schema → (EvalResult schema)
  | .unsupported => .unsupported
  | .supported packets => combineEvalResult (.supported packets) (postWith step packets)

/-- Stop iterating as soon as the reachable set stabilizes. The maximum
    number of iterations in `execute` comes from the cardinality proof. -/
private def saturateStar (step : schema.Packet → (EvalResult schema)) : Nat → (EvalResult schema) → (EvalResult schema)
  | 0, reached => reached
  | n + 1, reached =>
      let next := advanceStar step reached
      if next = reached then reached else saturateStar step n next

open Function in
private theorem saturateStar_eq_iterate (step : schema.Packet → (EvalResult schema))
    (n : Nat) (reached : EvalResult schema) :
    saturateStar step n reached = (advanceStar step)^[n] reached := by
  induction n generalizing reached with
  | zero => rfl
  | succ n ih =>
      rw [saturateStar, iterate_succ_apply]
      by_cases h : advanceStar step reached = reached
      · simp only [h, if_pos, iterate_fixed h n]
      · exact if_neg h ▸ ih _

open Function in
private theorem saturateStar_eq_boundedStarWith (step : schema.Packet → (EvalResult schema))
    (n : Nat) (σ : schema.Packet) :
    saturateStar step n (.supported {σ}) = boundedStarWith step n σ := by
  rw [saturateStar_eq_iterate]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ_apply', boundedStarWith, ih]
      cases h : boundedStarWith step n σ with
      | unsupported => rfl
      | supported reached =>
          cases hPost : postWith step reached <;> simp [advanceStar, hPost, combineEvalResult]

private theorem boundedStarWith_supported
    (step : schema.Packet → (EvalResult schema))
    (hstep : ∀ τ, ∃ A : Finset schema.Packet, step τ = .supported A) :
    ∀ n σ, ∃ B : Finset schema.Packet,
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

private def evalPredicate : Predicate schema → schema.Packet → (EvalResult schema)
  | .pFalse, _ => .supported ∅
  | .pTrue, σ => .supported {σ}
  | .pFieldEq ⟨f, v⟩, σ =>
      letI := schema.valueEq f
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

-- Compute the bound from the field cardinalities, without reducing the packet Fintype.
private def starFuel (schema : PacketSchema) : Nat :=
  letI := schema.fieldFinite
  letI := schema.valueFinite
  ∏ f : schema.Field, Fintype.card (schema.Value f)

private theorem starFuel_eq_card : starFuel schema = Fintype.card schema.Packet := by
  letI := schema.fieldEq
  letI := schema.fieldFinite
  letI := schema.valueFinite
  exact Fintype.card_pi.symm

mutual
  /-- Execute a NetKAT term on an input packet. -/
  def execute : NetKAT schema → schema.Packet → (EvalResult schema)
    | .drop, _ => .supported ∅
    | .id, σ => .supported {σ}
    | .test p, σ => evalPredicate p σ
    | .assign1 f v, σ => .supported {schema.model.update f v σ}
    | .union n₁ n₂, σ =>
        match execute n₁ σ, execute n₂ σ with
        | .supported outputs₁, .supported outputs₂ =>
            .supported (outputs₁ ∪ outputs₂)
        | _, _ => .unsupported
    | .seq p q, σ =>
        match execute p σ with
        | .unsupported => .unsupported
         | .supported A => evalSeq q A.1
    | .star p, σ => saturateStar (execute p) (starFuel schema) (.supported {σ})
    | .completeTest α, σ =>
        if σ = α then .supported {σ} else .supported ∅

  /-- Evaluate the second operand on each reachable intermediate packet. -/
  def evalSeq : NetKAT schema → Multiset schema.Packet → (EvalResult schema)
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
def post (p : NetKAT schema) (packets : Finset schema.Packet) : EvalResult schema :=
  evalSeq p packets.1

private theorem evalSeqWith_execute_eq (q : NetKAT schema) (packets : Multiset schema.Packet) :
    evalSeqWith (execute q) packets = evalSeq q packets := by
  simp [evalSeqWith, evalSeq]

private theorem postWith_execute_eq (q : NetKAT schema) (packets : Finset schema.Packet) :
    postWith (execute q) packets = post q packets := by
  simp [postWith, post, evalSeqWith_execute_eq]

/-- Executable reachability through at most a bounded number of policy steps.

    The evaluator keeps `unsupported` distinct from a supported empty set at
    every iteration, so an unsupported required execution is never discarded.
-/
def boundedStar (p : NetKAT schema) : Nat → schema.Packet → (EvalResult schema)
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
    (p : NetKAT schema) (σ : schema.Packet) :
    execute (.star p) σ =
      boundedStar p (Fintype.card schema.Packet) σ := by
  rw [execute, saturateStar_eq_boundedStarWith, starFuel_eq_card]
  induction Fintype.card schema.Packet generalizing σ with
  | zero => rfl
  | succ n ih =>
      rw [boundedStarWith, boundedStar, ih]
      cases h : boundedStar p n σ with
      | unsupported => simp [h]
      | supported packets =>
          simp only [h]
          rw [postWith_execute_eq]

/-- Zero iterations reach exactly the input packet. -/
theorem boundedStar_zero (p : NetKAT schema) (σ : schema.Packet) :
    boundedStar p 0 σ = .supported {σ} := by
  rfl

/-- A supported predecessor and supported post-step yield the union recurrence. -/
theorem boundedStar_succ_supported
    (p : NetKAT schema) (n : Nat) (σ : schema.Packet)
    (A B : Finset schema.Packet)
    (hA : boundedStar p n σ = .supported A)
    (hB : post p A = .supported B) :
    boundedStar p (n + 1) σ = .supported (A ∪ B) := by
  simp [boundedStar, hA, hB]

/-- An unsupported predecessor propagates through the next bounded iteration. -/
theorem boundedStar_succ_unsupported_previous
    (p : NetKAT schema) (n : Nat) (σ : schema.Packet)
    (hA : boundedStar p n σ = .unsupported) :
    boundedStar p (n + 1) σ = .unsupported := by
  simp [boundedStar, hA]

/-- An unsupported post-step propagates through the next bounded iteration. -/
theorem boundedStar_succ_unsupported_post
    (p : NetKAT schema) (n : Nat) (σ : schema.Packet)
    (A : Finset schema.Packet)
    (hA : boundedStar p n σ = .supported A)
    (hB : post p A = .unsupported) :
    boundedStar p (n + 1) σ = .unsupported := by
  simp [boundedStar, hA, hB]

/-- Supported reachable sets are monotone from one bounded iteration to the next. -/
theorem boundedStar_monotone
    (p : NetKAT schema) (n : Nat) (σ : schema.Packet)
    (A B : Finset schema.Packet)
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
theorem execute_drop (σ : schema.Packet) :
    execute .drop σ = .supported ∅ := by
  simp [execute]

/-- Executing `id` computes the singleton containing its input packet. -/
theorem execute_id (σ : schema.Packet) :
    execute .id σ = .supported {σ} := by
  simp [execute]

/-- Executing a primitive assignment computes its updated packet. -/
theorem execute_assign1 (f : schema.Field) (v : schema.Value f) (σ : schema.Packet) :
    execute (.assign1 f v) σ = .supported {schema.model.update f v σ} := by
  simp [execute]

/-- Executing a complete test keeps a matching packet and rejects a nonmatching
    packet with a supported empty result. -/
theorem execute_completeTest (α : schema.Packet) (σ : schema.Packet) :
    execute (.completeTest α) σ =
      if σ = α then .supported {σ} else .supported ∅ := by
  simp [execute]

/-- Executing a matching primitive field-equality test keeps its input packet. -/
theorem execute_fieldTestFor_match (f : schema.Field) (v : schema.Value f) (σ : schema.Packet)
    (h : σ f = v) :
    execute (NetKAT.fieldTestFor f v) σ = .supported {σ} := by
  simp [execute, evalPredicate, NetKAT.fieldTestFor, h]

/-- Executing a nonmatching primitive field-equality test produces no packets. -/
theorem execute_fieldTestFor_nonmatch (f : schema.Field) (v : schema.Value f) (σ : schema.Packet)
    (h : σ f ≠ v) :
    execute (NetKAT.fieldTestFor f v) σ = .supported ∅ := by
  simp [execute, evalPredicate, NetKAT.fieldTestFor, h]

theorem execute_fieldTest_match (f : FieldName) (v : FieldValueEnum) (σ : CtxPkt)
    (h : σ f = v) : execute (NetKAT.fieldTest f v) σ = .supported {σ} :=
  execute_fieldTestFor_match (schema := ctxSchema) f v σ h

theorem execute_fieldTest_nonmatch (f : FieldName) (v : FieldValueEnum) (σ : CtxPkt)
    (h : σ f ≠ v) : execute (NetKAT.fieldTest f v) σ = .supported ∅ :=
  execute_fieldTestFor_nonmatch (schema := ctxSchema) f v σ h

/-- Executing a union of two supported terms unions their computed outputs. -/
theorem execute_union_supported (n₁ n₂ : NetKAT schema) (σ : schema.Packet)
    (outputs₁ outputs₂ : Finset schema.Packet)
    (h₁ : execute n₁ σ = .supported outputs₁)
    (h₂ : execute n₂ σ = .supported outputs₂) :
    execute (.union n₁ n₂) σ = .supported (outputs₁ ∪ outputs₂) := by
  simp [execute, h₁, h₂]

/-- An unsupported left operand makes union evaluation unsupported. -/
theorem execute_union_unsupported_left (n₁ n₂ : NetKAT schema) (σ : schema.Packet)
    (h₁ : execute n₁ σ = .unsupported) :
    execute (.union n₁ n₂) σ = .unsupported := by
  simp [execute, h₁]

/-- An unsupported right operand makes union evaluation unsupported. -/
theorem execute_union_unsupported_right (n₁ n₂ : NetKAT schema) (σ : schema.Packet)
    (h₂ : execute n₂ σ = .unsupported) :
    execute (.union n₁ n₂) σ = .unsupported := by
  simp [execute, h₂]

/-- Sequential execution exposes the finite second-stage fold after the first
    operand has produced a supported intermediate set. -/
theorem execute_seq_supported (p q : NetKAT schema) (σ : schema.Packet)
    (A : Finset schema.Packet)
    (h₁ : execute p σ = .supported A) :
    execute (.seq p q) σ = evalSeq q A.1 := by
  simp [execute, h₁]

/-- An unsupported first operand propagates through sequential composition. -/
theorem execute_seq_unsupported_left (p q : NetKAT schema) (σ : schema.Packet)
    (h₁ : execute p σ = .unsupported) :
    execute (.seq p q) σ = .unsupported := by
  simp [execute, h₁]

/-- The empty intermediate set is a supported empty result; the second operand
    is not evaluated. -/
theorem execute_seq_empty (p q : NetKAT schema) (σ : schema.Packet)
    (h₁ : execute p σ = .supported (∅ : Finset schema.Packet)) :
    execute (.seq p q) σ = .supported ∅ := by
  rw [execute_seq_supported p q σ ∅ h₁]
  simp [evalSeq]

/-- A required unsupported second-stage evaluation propagates.  The hypothesis
    is phrased directly in terms of the executable fold, avoiding any claim
    about unreachable packets. -/
theorem execute_seq_unsupported_right (p q : NetKAT schema) (σ : schema.Packet)
    (A : Finset schema.Packet)
    (h₁ : execute p σ = .supported A)
    (h₂ : evalSeq q A.1 = .unsupported) :
    execute (.seq p q) σ = .unsupported := by
  rw [execute_seq_supported p q σ A h₁]
  exact h₂

/-- Compositional correctness for a supported sequential evaluation.  The
    executable first-stage result is `A`; `B` is the result of evaluating the
    second stage over exactly those reachable packets. -/
theorem execute_seq_correct
    (p q : NetKAT schema) (σ r : schema.Packet)
    (A B : Finset schema.Packet)
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
theorem execute_drop_correct (σ q : schema.Packet) :
    Semantics .drop σ q ↔
      q ∈ (match execute .drop σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  simp [execute, Semantics]

/-- The executable `id` result has exactly the denotational outputs. -/
theorem execute_id_correct (σ q : schema.Packet) :
    Semantics .id σ q ↔
      q ∈ (match execute .id σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  simp [execute, Semantics, eq_comm]

/-- The executable primitive-assignment result has exactly the denotational
    assignment outputs, in both directions. -/
theorem execute_assign1_correct (f : schema.Field) (v : schema.Value f)
    (σ q : schema.Packet) :
    Semantics (.assign1 f v) σ q ↔
      q ∈ (match execute (.assign1 f v) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  simp [execute, Semantics]

/-- The executable complete-test result agrees exactly with its relational
    semantics, for both matching and nonmatching packets. -/
theorem execute_completeTest_correct (α : schema.Packet) (σ q : schema.Packet) :
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
theorem execute_fieldTest_correct (f : schema.Field) (v : schema.Value f)
    (σ q : schema.Packet) :
    Semantics (NetKAT.fieldTestFor f v) σ q ↔
      q ∈ (match execute (NetKAT.fieldTestFor f v) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  rw [fieldTestFor_sem]
  by_cases h : σ f = v
  · simp [execute, evalPredicate, NetKAT.fieldTestFor, h]
  · simp [execute, evalPredicate, NetKAT.fieldTestFor, h]

/-- The executable false-predicate result has exactly the empty denotational
    relation. -/
theorem execute_pFalse_correct (σ q : schema.Packet) :
    Semantics (.test Predicate.pFalse) σ q ↔
      q ∈ (match execute (.test Predicate.pFalse) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  simp [execute, evalPredicate, Semantics, Predicate.holds, Predicate.eval]

/-- Executing the true predicate computes the singleton containing its input. -/
theorem execute_pTrue (σ : schema.Packet) :
    execute (.test Predicate.pTrue) σ = .supported {σ} := by
  simp [execute, evalPredicate]

/-- The executable true-predicate result has exactly the identity relation. -/
theorem execute_pTrue_correct (σ q : schema.Packet) :
    Semantics (.test Predicate.pTrue) σ q ↔
      q ∈ (match execute (.test Predicate.pTrue) σ with
        | .supported packets => packets
        | .unsupported => ∅) := by
  simp [execute, evalPredicate, Semantics, Predicate.holds, Predicate.eval, eq_comm]

/-- A conjunction of supported component evaluations keeps the input packet
    exactly when both component outputs contain it. -/
theorem execute_pAnd_supported
    (a b : Predicate schema) (σ : schema.Packet) (A B : Finset schema.Packet)
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
    (a b : Predicate schema) (σ q : schema.Packet) (A B : Finset schema.Packet)
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
    (a b : Predicate schema) (σ : schema.Packet) (A B : Finset schema.Packet)
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
    (a b : Predicate schema) (σ q : schema.Packet) (A B : Finset schema.Packet)
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
    (a : Predicate schema) (σ : schema.Packet) (A : Finset schema.Packet)
    (h : execute (.test a) σ = .supported A) :
    execute (.test (.pNot a)) σ =
      if σ ∈ A then .supported ∅ else .supported {σ} := by
  have h' : evalPredicate a σ = .supported A := by
    simpa [execute] using h
  simp [execute, evalPredicate, h']

/-- Every predicate test evaluates to a supported finite output set. -/
theorem execute_test_supported
    (a : Predicate schema) (σ : schema.Packet) :
    ∃ A : Finset schema.Packet,
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
    (p : NetKAT schema) (σ : schema.Packet) :
    ∃ B : Finset schema.Packet,
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
      exact ⟨{schema.model.update f v σ}, by simp [execute]
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
        (starFuel schema) σ
      exact ⟨B, by simpa only [execute, saturateStar_eq_boundedStarWith] using hB⟩

/- A supported, semantically correct predicate negation agrees with the
   relational negation semantics. -/
theorem execute_pNot_correct
    (a : Predicate schema) (σ q : schema.Packet) (A : Finset schema.Packet)
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
    (a : Predicate schema) (σ : schema.Packet) :
    ∃ A : Finset schema.Packet,
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
        simpa [NetKAT.fieldTestFor, execute, evalPredicate, Semantics,
          Predicate.holds, Predicate.eval, h, eq_comm]
      · refine ⟨∅, by simp [execute, evalPredicate, h], ?_⟩
        intro q
        simpa [NetKAT.fieldTestFor, execute, evalPredicate, Semantics,
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
theorem execute_union_correct (n₁ n₂ : NetKAT schema) (σ q : schema.Packet)
    (outputs₁ outputs₂ : Finset schema.Packet)
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
    (p : NetKAT schema) (A B : Finset schema.Packet)
    (hpost : post p A = .supported B)
    (hEval : ∀ σ, σ ∈ A → ∃ outputs,
      execute p σ = .supported outputs ∧
        ∀ τ, Semantics p σ τ ↔ τ ∈ outputs) :
    ∀ τ, τ ∈ B ↔ ∃ σ, σ ∈ A ∧ Semantics p σ τ := by
  have hfold : ∀ packets : Multiset schema.Packet,
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
def ReachableWithin (p : NetKAT schema) : Nat → schema.Packet → schema.Packet → Prop
  | 0, σ, τ => τ = σ
  | n + 1, σ, τ =>
      ReachableWithin p n σ τ ∨
        ∃ ρ, ReachableWithin p n σ ρ ∧ Semantics p ρ τ

/-- Zero iterations reach exactly the input packet. -/
theorem reachableWithin_zero_iff (p : NetKAT schema) (σ τ : schema.Packet) :
    ReachableWithin p 0 σ τ ↔ τ = σ := by
  rfl

/-- One more bounded iteration either keeps a packet already reachable, or
    takes one policy step from a packet reachable at the smaller bound. -/
theorem reachableWithin_succ_iff (p : NetKAT schema) (n : Nat) (σ τ : schema.Packet) :
    ReachableWithin p (n + 1) σ τ ↔
      ReachableWithin p n σ τ ∨
        ∃ ρ, ReachableWithin p n σ ρ ∧ Semantics p ρ τ := by
  rfl

private theorem reachableWithin_weaken
    (p : NetKAT schema) {n k : Nat} (h : n ≤ k) {σ τ : schema.Packet} :
    ReachableWithin p n σ τ → ReachableWithin p k σ τ := by
  intro hreach
  induction h with
  | refl => exact hreach
  | @step k h ih => exact Or.inl ih

private theorem reachableWithin_prepend
    (p : NetKAT schema) {n : Nat} {σ ρ τ : schema.Packet} :
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
    (p : NetKAT schema) (σ τ : schema.Packet) :
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
    (p : NetKAT schema) (σ τ : schema.Packet) :
    Semantics (.star p) σ τ ↔
      ∃ n : Nat, ReachableWithin p n σ τ := by
  exact starClosure_iff_reachableWithin p σ τ

 /-- Once one bounded reachability step adds no packets, the next step adds no
    packets either. -/
theorem reachableWithin_stable_succ
    (p : NetKAT schema) (n : Nat) (σ : schema.Packet)
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
    (p : NetKAT schema) (n k : Nat) (σ : schema.Packet)
    (hstable : ∀ τ, ReachableWithin p (n + 1) σ τ ↔
      ReachableWithin p n σ τ) (h : n ≤ k) :
    ∀ τ, ReachableWithin p (k + 1) σ τ ↔
      ReachableWithin p k σ τ := by
  induction h with
  | refl => exact hstable
  | @step k h ih =>
      exact reachableWithin_stable_succ p k σ ih

/-- An ascending chain of nonempty reachable sets has an adjacent stable pair
    by the cardinality of its ambient type. Only the sizes of the chain's
    sets enter the growth argument. -/
private theorem finiteGrowth_stabilizes {α : Type*} [Fintype α]
    (reached : Nat → Set α) (start : (reached 0).Nonempty)
    (grow : ∀ n, reached n ⊆ reached (n + 1)) :
    ∃ n ≤ Fintype.card α, reached (n + 1) = reached n := by
  by_contra! h
  have lower (k : Nat) (hk : k ≤ Fintype.card α) : k + 1 ≤ (reached k).ncard := by
    induction k with
    | zero => exact (Set.ncard_pos (Set.toFinite _)).mpr start
    | succ k ih =>
        have hk' := (Nat.le_succ k).trans hk
        have strict := Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨grow k, Ne.symm (h k hk')⟩)
        have := ih hk'
        omega
  have upper := Set.ncard_le_ncard (Set.subset_univ (reached (Fintype.card α)))
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at upper
  have := lower (Fintype.card α) le_rfl
  omega

/-- Bounded reachability stabilizes without constructing a packet finset. -/
theorem reachableWithin_finite_stabilizes
    (p : NetKAT schema) (σ : schema.Packet) :
    ∃ n, n ≤ Fintype.card schema.Packet ∧
      ∀ τ, ReachableWithin p (n + 1) σ τ ↔
        ReachableWithin p n σ τ := by
  let reached (n : Nat) : Set schema.Packet := {τ | ReachableWithin p n σ τ}
  obtain ⟨n, hn, hs⟩ := finiteGrowth_stabilizes reached ⟨σ, rfl⟩
    (fun n _ h => reachableWithin_weaken p (Nat.le_succ n) h)
  exact ⟨n, hn, fun τ => Set.ext_iff.mp hs τ⟩

theorem reachableWithin_stable_at_card
    (p : NetKAT schema) (σ : schema.Packet) :
    ∀ τ,
      ReachableWithin p
        (Fintype.card schema.Packet + 1) σ τ ↔
      ReachableWithin p
        (Fintype.card schema.Packet) σ τ := by
  obtain ⟨n, hn, hstable⟩ := reachableWithin_finite_stabilizes p σ
  exact reachableWithin_stable_of_le p n (Fintype.card schema.Packet) σ hstable hn

private theorem reachableWithin_stable_back
    (p : NetKAT schema) (n k : Nat) (σ : schema.Packet)
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
    (p : NetKAT schema) (σ τ : schema.Packet) :
    (∃ n : Nat, ReachableWithin p n σ τ) ↔
      ReachableWithin p (Fintype.card schema.Packet) σ τ := by
  constructor
  · rintro ⟨n, hreach⟩
    by_cases hle : n ≤ Fintype.card schema.Packet
    · exact reachableWithin_weaken p hle hreach
    · have hcard : Fintype.card schema.Packet ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hle)
      have hstable := reachableWithin_stable_at_card p σ
      exact reachableWithin_stable_back p (Fintype.card schema.Packet) n σ hstable hcard τ hreach
  · intro hreach
    exact ⟨Fintype.card schema.Packet, hreach⟩

/-- A supported bounded computation denotes exactly its relationally reachable
    packets, provided every packet reached at the bound is supported and
    semantically correct for one further policy evaluation. -/
theorem boundedStar_correct
    (p : NetKAT schema) (n : Nat) (σ : schema.Packet) (B : Finset schema.Packet)
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
    (p : NetKAT schema) (σ : schema.Packet) (B : Finset schema.Packet)
    (hExec : execute (.star p) σ = .supported B)
    (hEval :
      ∀ ρ,
        ReachableWithin p (Fintype.card schema.Packet) σ ρ →
          ∃ outputs,
            execute p ρ = .supported outputs ∧
              ∀ τ, Semantics p ρ τ ↔ τ ∈ outputs) :
    ∀ τ, Semantics (.star p) σ τ ↔ τ ∈ B := by
  have hbound : boundedStar p (Fintype.card schema.Packet) σ = .supported B := by
    rw [← execute_star_eq_boundedStar p σ]
    exact hExec
  have hreach := boundedStar_correct p (Fintype.card schema.Packet) σ B hbound hEval
  intro τ
  rw [semantics_star_iff_reachableWithin, reachableWithin_iff_at_card]
  exact (hreach τ).symm

/-- Every NetKAT policy evaluates to a supported finite set which is exactly its
    relational semantics, without any additional evaluator assumptions. -/
theorem execute_correct
    (p : NetKAT schema) (σ : schema.Packet) :
    ∃ B : Finset schema.Packet,
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
      refine ⟨{schema.model.update f v σ}, h, ?_⟩
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

/-- The executable finite output set equals the denotational output set. -/
theorem eval_correct (p : NetKAT schema) (σ : schema.Packet) :
    ∃ B : Finset schema.Packet, execute p σ = .supported B ∧ (B : Set schema.Packet) = eval p σ := by
  obtain ⟨B, hB, hSem⟩ := execute_correct p σ
  refine ⟨B, hB, Set.ext fun τ => ?_⟩
  exact (hSem τ).symm

end DyNetKAT.NetKAT
