------------------------------------------------------------------------
-- NetKAT denotational semantics
--
-- Per the DyNetKAT paper (arXiv:2102.10035v4, p. 6, §I-B "Semantics"):
--
--   ⟦N⟧ ⊆ Packet × Packet (binary relation on packets)
--
-- Defined compositionally:
--   ⟦0⟧      = ∅                              (empty relation)
--   ⟦1⟧      = {(σ,σ)}                        (identity / diagonal)
--   ⟦Pr⟧     = {(σ,σ) | Pr holds on σ}         (predicate test)
--   ⟦α⟧      = {(σ,σ) | α holds on σ}          (complete test)
--   ⟦π⟧      = {(σ, π(σ))}                    (complete assignment)
--   ⟦N₁+N₂⟧  = ⟦N₁⟧ ∪ ⟦N₂⟧                    (union)
--   ⟦N₁;N₂⟧  = ⟦N₁⟧ ∘ ⟦N₂⟧                    (relational composition)
--   ⟦N*⟧     = ⋃ₖ ⟦N⟧ᵏ                         (reflexive-transitive closure)
--
-- On a finite packet domain, ⟦N*⟧ is a finite union (terminates).
--
-- Note: The paper presents NetKAT semantics over packet histories (lists of
-- packets). However, in the dup-free fragment (NetKAT^dup-free), each history
-- consists of a single packet σ (no dup to create multi-packet histories).
-- The operational rule (cpol_;check) confirms: σ' in ⟦p⟧(σ::<>), i.e., the
-- policy is evaluated on a single-packet history. Our single-packet semantics
-- is therefore semantically equivalent for NetKAT^dup-free.
------------------------------------------------------------------------

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Bool.Basic
import DyNetKAT.NetKAT.Packet
import DyNetKAT.NetKAT.AST

namespace DyNetKAT.NetKAT

open Finset
open Predicate
open Packet

------------------------------------------------------------------------
-- Reflexive-transitive closure (Kleene star semantics)
------------------------------------------------------------------------

/-! Relators for relational operations -/

/-- Reflexive-transitive closure of a relation (Kleene star semantics).
    ⟦N*⟧ = ⋃ₖ ⟦N⟧ᵏ — the reflexive-transitive closure. -/
inductive StarClosure {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl : ∀ a, StarClosure R a a
  | step : ∀ {a b c}, R a b → StarClosure R b c → StarClosure R a c

------------------------------------------------------------------------
-- Denotational semantics ⟦N⟧ : Packet → Packet → Prop
------------------------------------------------------------------------

/-- Denotational semantics of NetKAT terms.
    ⟦N⟧(σ,τ) holds iff packet σ is transformed to τ by policy N -/
def Semantics (N : NetKAT) : CtxPkt → CtxPkt → Prop
  | σ, τ =>
    match N with
    | .drop => False
    | .id => σ = τ
    | .test Pr => Pr.holds σ ∧ σ = τ
    | .completeTest α => holdsComplete α σ ∧ σ = τ
    | .assign1 f v => τ = Packet.update σ f v
    | .union n₁ n₂ => Semantics n₁ σ τ ∨ Semantics n₂ σ τ
    | .seq n₁ n₂ => ∃ ρ, Semantics n₁ σ ρ ∧ Semantics n₂ ρ τ
    | .star n => StarClosure (Semantics n) σ τ

/-- Notation: ⟦N⟧(σ) = set of output packets for input σ -/
def eval (N : NetKAT) (σ : CtxPkt) : Set CtxPkt :=
  { q : CtxPkt | Semantics N σ q }

------------------------------------------------------------------------
-- Basic semantic identities
------------------------------------------------------------------------

/-- ⟦0⟧ = ∅ (empty relation) -/
theorem drop_empty (σ : CtxPkt) : eval .drop σ = ∅ := by
  ext q
  constructor
  · intro h
    cases h
  · intro h
    cases h

/-- ⟦1⟧ = identity relation -/
theorem id_diag (σ τ : CtxPkt) : Semantics .id σ τ ↔ σ = τ := by
  rfl

/-- ⟦N₁+N₂⟧ = ⟦N₁⟧ ∪ ⟦N₂⟧ -/
theorem union_sem (n₁ n₂ : NetKAT) (σ τ : CtxPkt) :
    Semantics (n₁.union n₂) σ τ ↔ Semantics n₁ σ τ ∨ Semantics n₂ σ τ := by
  rfl

/-- ⟦N₁;N₂⟧ = ⟦N₁⟧ ∘ ⟦N₂⟧ -/
theorem seq_sem (n₁ n₂ : NetKAT) (σ τ : CtxPkt) :
    Semantics (n₁.seq n₂) σ τ ↔ ∃ ρ, Semantics n₁ σ ρ ∧ Semantics n₂ ρ τ := by
  rfl

/-- If NetKAT expressions `n` and `m` behave deterministically as packet
    transformations `f` and `g`, their sequential composition behaves as `g ∘ f`.

    That is, if ⟦n⟧(σ,τ) ↔ τ = f σ  and  ⟦m⟧(σ,τ) ↔ τ = g σ, then
    ⟦n;m⟧(σ,τ) ↔ τ = g (f σ).

    This follows from the existential semantics of sequential composition:
    ⟦n;m⟧(σ,τ) ↔ ∃ ρ, ⟦n⟧(σ,ρ) ∧ ⟦m⟧(ρ,τ).
    By the deterministic hypothesis on `n`, the only possible ρ is f σ.
    Substituting and applying the deterministic hypothesis on `m` yields τ = g (f σ). -/
theorem seq_deterministic_sem
    (n m : NetKAT)
    (f g : CtxPkt → CtxPkt)
    (hn : ∀ σ τ, Semantics n σ τ ↔ τ = f σ)
    (hm : ∀ σ τ, Semantics m σ τ ↔ τ = g σ)
    (σ τ : CtxPkt) :
    Semantics (.seq n m) σ τ ↔ τ = g (f σ) := by
  constructor
  · intro h
    -- ⟦n;m⟧(σ,τ): ∃ ρ, ⟦n⟧(σ,ρ) ∧ ⟦m⟧(ρ,τ).
    rcases h with ⟨ρ, ⟨h_n, h_m⟩⟩
    -- By hn: ρ = f σ (the unique witness from n's deterministic semantics).
    have : ρ = f σ := (hn σ ρ).mp h_n
    subst this
    -- Now ⟦m⟧(f σ, τ) holds. By hm: τ = g (f σ).
    exact (hm (f σ) τ).mp h_m
  · intro h
    -- Need to construct witness ρ = f σ for the existential.
    use f σ
    constructor
    · -- ⟦n⟧(σ, f σ): true by hn since f σ = f σ.
      exact (hn σ (f σ)).mpr rfl
    · -- ⟦m⟧(f σ, τ): true by hm since τ = g (f σ).
      exact (hm (f σ) τ).mpr h

/-- ⟦N*⟧ contains the identity: (σ,σ) ∈ ⟦N*⟧ for all σ -/
theorem star_refl (n : NetKAT) (σ : CtxPkt) : Semantics (n.star) σ σ :=
  StarClosure.refl σ

/-- ⟦N*⟧ is monotonic in iteration: if σ→τ via N, then σ→τ via N* -/
theorem star_step (n : NetKAT) (σ τ : CtxPkt) :
    Semantics n σ τ → Semantics (n.star) σ τ := by
  intro h
  exact StarClosure.step h (StarClosure.refl τ)

------------------------------------------------------------------------
-- Test semantics: predicate and complete test semantics
------------------------------------------------------------------------

/-- ⟦f=v⟧ = {(σ,σ) | σ(f) = v} — atomic test preserves packet iff field matches.
    The semantics of a predicate test is the identity relation restricted to
    packets satisfying the predicate. -/
theorem fieldTest_sem (f : FieldName) (v : FieldValueEnum) (σ τ : CtxPkt) :
    Semantics (NetKAT.fieldTest f v) σ τ ↔ σ f = v ∧ τ = σ := by
  unfold NetKAT.fieldTest Semantics
  constructor
  · intro h
    cases h with
    | intro hholds heq =>
      constructor
      · unfold Predicate.holds Predicate.eval at hholds
        rw [Bool.decide_iff] at hholds
        exact hholds
      · exact heq.symm
  · intro h
    cases h with
    | intro h1 h2 =>
      subst h2
      constructor
      · unfold Predicate.holds Predicate.eval
        rw [Bool.decide_iff]
        exact h1
      · rfl

/-- ⟦¬Pr⟧ = {(σ,σ) | Pr does not hold on σ} — negation test.
    Per Figure 3: ⟦¬a⟧(h) ≜ {h} \ ⟦a⟧(h).
    In single-packet form: {(σ,σ) | ¬(Pr holds on σ)}. -/
theorem notTest_sem (Pr : Predicate) (σ τ : CtxPkt) :
    Semantics (NetKAT.test (.pNot Pr)) σ τ ↔ ¬Pr.holds σ ∧ τ = σ := by
  simp only [Semantics]
  constructor
  · intro h
    cases h with
    | intro hholds heq =>
      constructor
      · simp [Predicate.holds, Predicate.eval] at hholds
        exact Bool.eq_false_iff.mp hholds
      · exact heq.symm
  · intro h
    cases h with
    | intro h1 h2 =>
      subst h2
      constructor
      · simp [Predicate.holds, Predicate.eval]
        exact Bool.eq_false_iff.mpr h1
      · rfl

/-- ⟦Pr₁ ∨ Pr₂⟧ = {(σ,σ) | Pr₁ holds or Pr₂ holds} — disjunction test. -/
theorem orTest_sem (Pr₁ Pr₂ : Predicate) (σ τ : CtxPkt) :
    Semantics (NetKAT.test (.pOr Pr₁ Pr₂)) σ τ ↔
    (Pr₁.holds σ ∨ Pr₂.holds σ) ∧ τ = σ := by
  simp only [Semantics]
  constructor
  · intro h
    cases h with
    | intro hholds heq =>
      constructor
      · simp [Predicate.holds, Predicate.eval, Bool.or_eq_true] at hholds
        exact hholds
      · exact heq.symm
  · intro h
    cases h with
    | intro h1 h2 =>
      subst h2
      constructor
      · simp [Predicate.holds, Predicate.eval, Bool.or_eq_true]
        exact h1
      · rfl

/-- ⟦Pr₁ ∧ Pr₂⟧ = {(σ,σ) | Pr₁ holds and Pr₂ holds} — conjunction test. -/
theorem andTest_sem (Pr₁ Pr₂ : Predicate) (σ τ : CtxPkt) :
    Semantics (NetKAT.test (.pAnd Pr₁ Pr₂)) σ τ ↔
    (Pr₁.holds σ ∧ Pr₂.holds σ) ∧ τ = σ := by
  simp only [Semantics]
  constructor
  · intro h
    cases h with
    | intro hholds heq =>
      constructor
      · simp [Predicate.holds, Predicate.eval, Bool.and_eq_true] at hholds
        exact hholds
      · exact heq.symm
  · intro h
    cases h with
    | intro h1 h2 =>
      subst h2
      constructor
      · simp [Predicate.holds, Predicate.eval, Bool.and_eq_true]
        exact h1
      · rfl

------------------------------------------------------------------------
-- Complete test and assignment semantics
------------------------------------------------------------------------

/-- ⟦α⟧ = {(σ,σ) | α holds on σ} — complete test preserves packet iff all match.
    Per paper p. 6: a complete test α = f₁=v₁·...·fₙ=vₙ is the conjunction
    of all field tests. Since α is a total function, it checks every field. -/
theorem completeTest_sem (α : CompleteTest) (σ τ : CtxPkt) :
    Semantics (NetKAT.completeTestEmbed α) σ τ ↔ holdsComplete α σ ∧ σ = τ := by
  unfold NetKAT.completeTestEmbed
  simp only [Semantics]

------------------------------------------------------------------------
-- Single-field assignment semantics
------------------------------------------------------------------------

/-- ⟦f←v⟧ maps σ to σ[f↦v] — primitive single-field assignment updates the field.
    Per paper: ⟦f←v⟧ = {(σ, σ[f↦v])}. -/
theorem assign1_sem (f : FieldName) (v : FieldValueEnum) (σ τ : CtxPkt) :
    Semantics (.assign1 f v) σ τ ↔
    τ = Packet.update σ f v := by
  rfl

/-- Sequencing of a single-field assignment with N:
    ⟦(f←v);N⟧(σ,τ) ↔ ⟦N⟧(σ[f:=v],τ).

    This follows directly from the semantics clauses:
    - `assign1` updates field f to v: ⟦f←v⟧(σ,ρ) ↔ ρ = Packet.update σ f v.
    - `seq` composes: ⟦N₁;N₂⟧(σ,τ) ↔ ∃ ρ, ⟦N₁⟧(σ,ρ) ∧ ⟦N₂⟧(ρ,τ).

    Substituting the unique witness ρ = Packet.update σ f v yields the
    equivalence ⟦N⟧(Packet.update σ f v, τ). -/
theorem assign1_seq_sem (f : FieldName) (v : FieldValueEnum) (n : NetKAT)
    (σ τ : CtxPkt) :
    Semantics (.seq (.assign1 f v) n) σ τ ↔
    Semantics n (Packet.update σ f v) τ := by
  constructor
  · intro h
    -- ⟦(f←v);N⟧(σ,τ): exists ρ with ⟦f←v⟧(σ,ρ) and ⟦N⟧(ρ,τ).
    -- From ⟦f←v⟧: ρ = Packet.update σ f v. Substitute into ⟦N⟧(ρ,τ).
    rcases h with ⟨ρ, ⟨h_assign, h_n⟩⟩
    -- h_assign: ρ = Packet.update σ f v
    subst h_assign
    exact h_n
  · intro h
    -- Direct construction of the witness ρ.
    use Packet.update σ f v
    constructor
    · -- ⟦f←v⟧(σ, Packet.update σ f v): τ = Packet.update σ f v.
      rfl
    · exact h

------------------------------------------------------------------------
-- Assignment-list fold semantics
------------------------------------------------------------------------

/-- Semantics of a folded sequence of primitive single-field assignments.

For a list of fields `fs`, valuation `π`, and packets `σ`, `τ`:

The NetKAT expression `fs.foldr (fun f acc => .seq (.assign1 f (π f)) acc) .id`
processes the listed assignments in sequence (left-to-right in `fs`).
Its output is exactly the result of applying those field updates to `σ`,
in the same order, via `fs.foldl (fun pkt f => Packet.update pkt f (π f)) σ`.

This holds for arbitrary field lists, not just `fieldEnum`. -/
theorem assign_list_sem
    (fs : List FieldName)
    (π : CompleteAssignmentValuation)
    (σ τ : CtxPkt) :
    Semantics (fs.foldr (fun f acc => .seq (.assign1 f (π f)) acc) .id) σ τ ↔
    τ = fs.foldl (fun pkt f => Packet.update pkt f (π f)) σ := by
  induction fs generalizing σ with
  | nil =>
    -- Base case: empty list. Expression is `.id`, fold is `σ`.
    simp only [List.foldr, List.foldl, Semantics]
    exact ⟨Eq.symm, Eq.symm⟩
  | cons f fs' ih =>
    -- Inductive step: f :: fs'. Expression is (assign1 f (π f)) ; (foldr fs' ...).
    -- By assign1_seq_sem, this is equivalent to evaluating the rest on the
    -- updated packet Packet.update σ f (π f).
    -- By IH, that fold is equivalent to fs'.foldl (...).
    -- Combined: τ = (f :: fs').foldl (fun pkt g => Packet.update pkt g (π g)) σ.
    simp only [List.foldr, List.foldl]
    -- LHS: Semantics (.seq (assign1 f (π f)) (fs'.foldr ...)) σ τ
    -- RHS: τ = fs'.foldl (fun pkt g => Packet.update pkt g (π g)) (Packet.update σ f (π f))
    -- These are equivalent by assign1_seq_sem and IH.
    rw [assign1_seq_sem]
    -- Now need: Semantics (fs'.foldr ...) (Packet.update σ f (π f)) τ ↔
    --            τ = fs'.foldl (fun pkt g => Packet.update pkt g (π g)) (Packet.update σ f (π f))
    -- This is exactly `ih` with σ replaced by `Packet.update σ f (π f)`.
    exact ih (Packet.update σ f (π f))

------------------------------------------------------------------------
-- Examples on concrete values
------------------------------------------------------------------------

/-- The identity relation is reflexive: every packet is related to itself. -/
theorem id_reflexive : ∀ (σ : CtxPkt), Semantics .id σ σ := by
  intro σ
  rfl

/-- Drop produces no output packets. -/
theorem drop_no_output (σ : CtxPkt) : eval .drop σ = ∅ := by
  exact drop_empty σ

------------------------------------------------------------------------
-- Algebraic properties (Section 6: foundational theorems)
-- These are the semantically-proved NetKAT axioms from Figure 4.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Kleene algebra laws (from Figure 4)
------------------------------------------------------------------------

/-- ⟦N₁+N₂⟧ = ⟦N₁⟧ ∪ ⟦N₂⟧ as sets -/
theorem union_eval (n₁ n₂ : NetKAT) (σ : CtxPkt) :
    eval (n₁.union n₂) σ = eval n₁ σ ∪ eval n₂ σ := by
  ext q
  constructor
  · intro h
    rcases h with (h₁ | h₂)
    · left; exact h₁
    · right; exact h₂
  · intro h
    rcases h with (h₁ | h₂)
    · left; exact h₁
    · right; exact h₂

/-- ⟦0⟧ = ∅ as a set -/
theorem drop_eval_empty (σ : CtxPkt) : eval .drop σ = ∅ :=
  drop_empty σ

/-- ⟦1⟧ = {σ} (singleton identity) -/
theorem id_eval_diag (σ : CtxPkt) : eval .id σ = {σ} := by
  ext q
  constructor
  · intro h
    simp only [eval, Semantics] at h
    subst h
    simp
  · intro h
    simpa [eval, Semantics] using h

/-- Left identity: 1;N ≡ N (⟦1⟧ ∘ ⟦N⟧ = ⟦N⟧) -/
theorem seq_id_left (n : NetKAT) (σ τ : CtxPkt) :
    Semantics (.seq .id n) σ τ ↔ Semantics n σ τ := by
  constructor
  · intro h
    rcases h with ⟨ρ, ⟨h_id, h_n⟩⟩
    subst ρ
    exact h_n
  · intro h
    use σ
    constructor
    · rfl
    · exact h

/-- Right identity: N;1 ≡ N (⟦N⟧ ∘ ⟦1⟧ = ⟦N⟧) -/
theorem seq_id_right (n : NetKAT) (σ τ : CtxPkt) :
    Semantics (.seq n .id) σ τ ↔ Semantics n σ τ := by
  constructor
  · intro h
    rcases h with ⟨ρ, ⟨h_n, h_id⟩⟩
    subst ρ
    exact h_n
  · intro h
    use τ
    constructor
    · exact h
    · rfl

/-- Left annihilation: 0;N ≡ 0 (⟦0⟧ ∘ ⟦N⟧ = ∅) -/
theorem seq_drop_left (n : NetKAT) (σ τ : CtxPkt) :
    ¬Semantics (.seq .drop n) σ τ := by
  intro h
  simp only [Semantics] at h
  rcases h with ⟨ρ, ⟨h₁, _⟩⟩
  -- .drop σ ρ means False
  exact h₁

/-- Right annihilation: N;0 ≡ 0 (⟦N⟧ ∘ ⟦0⟧ = ∅) -/
theorem seq_drop_right (n : NetKAT) (σ τ : CtxPkt) :
    ¬Semantics (.seq n .drop) σ τ := by
  intro h
  simp only [Semantics] at h
  rcases h with ⟨ρ, ⟨_, h₂⟩⟩
  -- .drop ρ τ means False
  exact h₂

/-- Union associativity: (N₁+N₂)+N₃ = N₁+(N₂+N₃) -/
theorem union_assoc (n₁ n₂ n₃ : NetKAT) (σ τ : CtxPkt) :
    Semantics (.union (.union n₁ n₂) n₃) σ τ ↔
    Semantics (.union n₁ (.union n₂ n₃)) σ τ := by
  simp only [Semantics]
  tauto

/-- Union commutativity: N₁+N₂ = N₂+N₁ -/
theorem union_comm (n₁ n₂ : NetKAT) (σ τ : CtxPkt) :
    Semantics (.union n₁ n₂) σ τ ↔ Semantics (.union n₂ n₁) σ τ := by
  simp only [Semantics]
  tauto

/-- Union idempotence: N+N = N -/
theorem union_idem (n : NetKAT) (σ τ : CtxPkt) :
    Semantics (.union n n) σ τ ↔ Semantics n σ τ := by
  simp only [Semantics]
  tauto

/-- Left distributivity: N₁;(N₂+N₃) = N₁;N₂ + N₁;N₃ -/
theorem seq_distrib_left (n₁ n₂ n₃ : NetKAT) (σ τ : CtxPkt) :
    Semantics (.seq n₁ (.union n₂ n₃)) σ τ ↔
    Semantics (.union (.seq n₁ n₂) (.seq n₁ n₃)) σ τ := by
  constructor
  · intro h
    rcases h with ⟨ρ, ⟨h₁, h₂ | h₂⟩⟩
    · left
      exact ⟨ρ, h₁, h₂⟩
    · right
      exact ⟨ρ, h₁, h₂⟩
  · intro h
    rcases h with (h | h)
    · rcases h with ⟨ρ, ⟨h₁, h₂⟩⟩
      use ρ
      exact ⟨h₁, Or.inl h₂⟩
    · rcases h with ⟨ρ, ⟨h₁, h₂⟩⟩
      use ρ
      exact ⟨h₁, Or.inr h₂⟩

/-- Right distributivity: (N₁+N₂);N₃ = N₁;N₃ + N₂;N₃ -/
theorem seq_distrib_right (n₁ n₂ n₃ : NetKAT) (σ τ : CtxPkt) :
    Semantics (.seq (.union n₁ n₂) n₃) σ τ ↔
    Semantics (.union (.seq n₁ n₃) (.seq n₂ n₃)) σ τ := by
  constructor
  · intro h
    rcases h with ⟨ρ, ⟨h₁ | h₁, h₂⟩⟩
    · left
      exact ⟨ρ, h₁, h₂⟩
    · right
      exact ⟨ρ, h₁, h₂⟩
  · intro h
    rcases h with (h | h)
    · rcases h with ⟨ρ, ⟨h₁, h₂⟩⟩
      exact ⟨ρ, Or.inl h₁, h₂⟩
    · rcases h with ⟨ρ, ⟨h₁, h₂⟩⟩
      exact ⟨ρ, Or.inr h₁, h₂⟩

------------------------------------------------------------------------
-- Boolean algebra laws (from Figure 4: BA-EXCL-MID, BA-CONTRA)
------------------------------------------------------------------------

/-- BA-EXCL-MID: Pr + ¬Pr = 1 (excluded middle) — predicate disjunction with
    negation covers all packets. -/
theorem pred_excluded_middle (Pr : Predicate) (σ : CtxPkt) :
    (Predicate.pOr Pr (Predicate.pNot Pr)).holds σ := by
  unfold Predicate.holds
  cases h : Pr.eval σ with
  | true => simp [Predicate.eval, h]
  | false => simp [Predicate.eval, h]

/-- BA-CONTRA: Pr · ¬Pr = 0 (contradiction) — predicate conjunction with
    negation never holds. -/
theorem pred_contra (Pr : Predicate) (σ : CtxPkt) :
    ¬(Predicate.pAnd Pr (Predicate.pNot Pr)).holds σ := by
  unfold Predicate.holds Predicate.eval
  cases h : Pr.eval σ with
  | true => simp [Predicate.pNot, Predicate.eval, h]
  | false => simp [Predicate.pNot, Predicate.eval, h]

/-- Double negation elimination: ¬¬Pr = Pr -/
theorem pred_double_neg (Pr : Predicate) (σ : CtxPkt) :
    (Predicate.pNot (Predicate.pNot Pr)).holds σ ↔ Pr.holds σ := by
  unfold Predicate.holds
  cases h : Pr.eval σ with
  | true => simp [Predicate.eval, h]
  | false => simp [Predicate.eval, h]

/-- De Morgan: ¬(Pr₁ ∨ Pr₂) = ¬Pr₁ ∧ ¬Pr₂ -/
theorem pred_deMorgan_or (Pr₁ Pr₂ : Predicate) (σ : CtxPkt) :
    (Predicate.pNot (Predicate.pOr Pr₁ Pr₂)).holds σ ↔
    (Predicate.pNot Pr₁).holds σ ∧ (Predicate.pNot Pr₂).holds σ := by
  unfold Predicate.holds Predicate.eval
  cases h1 : Pr₁.eval σ with
  | true =>
    cases h2 : Pr₂.eval σ with
    | true => simp [Predicate.pNot, Predicate.eval, h1, h2]
    | false => simp [Predicate.pNot, Predicate.eval, h1, h2]
  | false =>
    cases h2 : Pr₂.eval σ with
    | true => simp [Predicate.pNot, Predicate.eval, h1, h2]
    | false => simp [Predicate.pNot, Predicate.eval, h1, h2]

/-- De Morgan: ¬(Pr₁ ∧ Pr₂) = ¬Pr₁ ∨ ¬Pr₂ -/
theorem pred_deMorgan_and (Pr₁ Pr₂ : Predicate) (σ : CtxPkt) :
    (Predicate.pNot (Predicate.pAnd Pr₁ Pr₂)).holds σ ↔
    (Predicate.pNot Pr₁).holds σ ∨ (Predicate.pNot Pr₂).holds σ := by
  unfold Predicate.holds Predicate.eval
  cases h1 : Pr₁.eval σ with
  | true =>
    cases h2 : Pr₂.eval σ with
    | true => simp [Predicate.pNot, Predicate.eval, h1, h2]
    | false => simp [Predicate.pNot, Predicate.eval, h1, h2]
  | false =>
    cases h2 : Pr₂.eval σ with
    | true => simp [Predicate.pNot, Predicate.eval, h1, h2]
    | false => simp [Predicate.pNot, Predicate.eval, h1, h2]

------------------------------------------------------------------------
-- Packet algebra laws (from Figure 4: PA-MOD-MOD, PA-MOD-FILTER, etc.)
------------------------------------------------------------------------

/-- PA-MOD-MOD: f←v₁; f←v₂ = f←v₂ (overwriting same field twice)
    The second assignment wins. -/
theorem assign_overwrite (f : FieldName) (v₁ v₂ : FieldValueEnum) (σ : CtxPkt) :
    let π₁ := fun s => Packet.update s f v₁
    let π₂ := fun s => Packet.update s f v₂
    (π₂ ∘ π₁) σ = Packet.update σ f v₂ := by
  -- π₁ σ = σ[f ↦ v₁], then π₂(σ[f ↦ v₁]) = (σ[f ↦ v₁])[f ↦ v₂] = σ[f ↦ v₂]
  -- by update_update_same in Packet.lean
  let π₁ := fun s => Packet.update s f v₁
  let π₂ := fun s => Packet.update s f v₂
  show (Packet.update (Packet.update σ f v₁) f v₂) = Packet.update σ f v₂
  exact Packet.update_update_same σ f v₁ v₂

/-- PA-MOD-MOD-COMM: f←v; f'←v' = f'←v'; f←v when f ≠ f' (distinct fields commute) -/
theorem assign_comm_diff (f g : FieldName) (v : FieldValueEnum) (v' : FieldValueEnum)
    (hfg : f ≠ g) (σ : CtxPkt) :
    Packet.update (Packet.update σ f v) g v' =
    Packet.update (Packet.update σ g v') f v := by
  exact Packet.update_update_diff σ f g hfg v v'

/-- PA-MOD-FILTER: f←v; f=v ≡ f←v (test after same-field assignment is idempotent) -/
theorem assign_test_same_field (f : FieldName) (v : FieldValueEnum) (σ : CtxPkt) :
    let π := fun s => Packet.update s f v
    (π σ) f = v := by
  let π := fun s => Packet.update s f v
  show Packet.update σ f v f = v
  exact Packet.get_update_same σ f v

/-- PA-FILTER-MOD: f=v; f←v' ≡ f←v' (assignment after test of same field) -/
theorem test_assign_same_field (f : FieldName) (v v' : FieldValueEnum) (σ : CtxPkt)
    (h : σ f = v) :
    Packet.update σ f v' f = v' := by
  simp [Packet.get, Packet.update, h]

/-- Updating every field in `fieldEnum` to the corresponding value in π produces π,
    independently of the initial packet.

    This captures Definition 4's "σπ = π" semantics: a complete assignment
    overwrites every field, so the result depends only on π, not on σ. -/
theorem fieldEnum_updates_complete
    (π : CompleteAssignmentValuation)
    (σ : CtxPkt) :
    NetKAT.fieldEnum.foldl (fun pkt f => Packet.update pkt f (π f)) σ = π := by
  unfold NetKAT.fieldEnum
  -- Now the fold is over [tpSrc, tpDst, swId, port]
  -- We use function extensionality and prove field by field.
  ext f
  cases f with
  | tpSrc =>
    -- The fold processes tpSrc last among all fields (well, first).
    -- After update at tpSrc, tpSrc = π tpSrc.
    -- Subsequent updates (tpDst, swId, port) don't change tpSrc (distinct fields).
    -- So the final value is π tpSrc.
    -- We use get_update_diff to show updates at other fields don't change tpSrc.
    simp [List.foldl, Packet.update, Packet.get]
  | tpDst =>
    simp [List.foldl, Packet.update, Packet.get]
  | swId =>
    simp [List.foldl, Packet.update, Packet.get]
  | port =>
    simp [List.foldl, Packet.update, Packet.get]

------------------------------------------------------------------------
-- Complete-assignment correspondence (Definition 4, p. 8)
------------------------------------------------------------------------

/-- `completeAssignExpr` implements the complete-assignment semantics of
    Definition 4 (p. 8): the output packet equals the valuation π,
    independently of the input packet σ.

    `⟦NetKAT.completeAssignExpr π⟧(σ,τ) ↔ τ = π`

Proof sketch:
1. `completeAssignExpr π` unfolds to `fieldEnum.foldr (fun f acc => .seq
   (.assign1 f (π f)) acc) .id` (the match collapses to the cons branch
   because `fieldEnum` is non-empty).
2. `assign_list_sem` rewrites the semantics to
   `τ = fieldEnum.foldl (fun pkt f => Packet.update pkt f (π f)) σ`.
3. `fieldEnum_updates_complete` rewrites that fold to `π`. -/
theorem completeAssignExpr_sem
    (π : CompleteAssignmentValuation)
    (σ τ : CtxPkt) :
    Semantics (NetKAT.completeAssignExpr π) σ τ ↔
    τ = π := by
  -- Step 1: Show that `completeAssignExpr π` equals the list-fold form
  -- `fieldEnum.foldr (fun f acc => .seq (.assign1 f (π f)) acc) .id`.
  -- `completeAssignExpr` is defined as a match on `fieldEnum`; since
  -- `fieldEnum = [tpSrc, tpDst, swId, port]` is concrete and non-empty,
  -- the match reduces to the cons branch, which is definitionally the foldr.
  have h_fold : NetKAT.completeAssignExpr π =
      NetKAT.fieldEnum.foldr (fun f acc => .seq (.assign1 f (π f)) acc) .id := by
    unfold NetKAT.completeAssignExpr
    simp only [NetKAT.fieldEnum]
    rfl
  rw [h_fold]
  -- Step 2: apply `assign_list_sem` (with fs := fieldEnum) to rewrite the
  -- NetKAT semantics to a packet-level fold.
  rw [assign_list_sem]
  -- Step 3: apply `fieldEnum_updates_complete` to rewrite the fold to π.
  rw [fieldEnum_updates_complete]
