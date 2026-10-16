import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import DyNetKAT.NetKAT.Packet
import DyNetKAT.NetKAT.AST

namespace DyNetKAT.NetKAT

open Finset

------------------------------------------------------------------------
-- NetKAT denotational semantics
------------------------------------------------------------------------
-- Per the DyNetKAT paper (arXiv:2102.10035v4, p. 6, §I-B "Semantics"):
--
--   ⟦N⟧ ⊆ Packet × Packet (binary relation on packets)
--
-- Defined compositionally:
--   ⟦0⟧      = ∅                              (empty relation)
--   ⟦1⟧      = {(σ,σ)}                        (identity / diagonal)
--   ⟦f=v⟧    = {(σ,σ) | σ(f) = v}             (test: identity on passing packets)
--   ⟦α⟧      = ∩_{f=v ∈ α} ⟦f=v⟧              (complete test = conjunction)
--   ⟦f←v⟧    = {(σ,σ[f↦v])}                    (assignment)
--   ⟦π⟧      = {(σ, π(σ))}                    (complete assignment)
--   ⟦N₁+N₂⟧  = ⟦N₁⟧ ∪ ⟦N₂⟧                    (union)
--   ⟦N₁;N₂⟧  = ⟦N₁⟧ ∘ ⟦N₂⟧                    (relational composition)
--   ⟦N*⟧     = ⋃ₖ ⟦N⟧ᵏ                         (reflexive-transitive closure)
--
-- On a finite packet domain, ⟦N*⟧ is a finite union (terminates).

/-! Relators for relational operations -/
namespace Semantics

/-- Reflexive-transitive closure of a relation (Kleene star semantics).
    ⟦N*⟧ = ⋃ₖ ⟦N⟧ᵏ — the reflexive-transitive closure. -/
inductive StarClosure {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl : ∀ a, StarClosure R a a
  | step : ∀ {a b c}, R a b → StarClosure R b c → StarClosure R a c

end Semantics

open Semantics

------------------------------------------------------------------------
-- Denotational semantics ⟦N⟧ : Packet → Packet → Prop
------------------------------------------------------------------------

/-- Denotational semantics of NetKAT terms.
    ⟦N⟧(σ,τ) holds iff packet σ is transformed to τ by policy N -/
def Semantics (N : NetKAT) : Packet → Packet → Prop
  | p, q =>
    match N with
    | .drop => False
    | .id => p = q
    | .test α => (∀ fe ∈ α, p fe.field = fe.value) ∧ p = q
    | .assign π => π p = q
    | .union n₁ n₂ => Semantics n₁ p q ∨ Semantics n₂ p q
    | .seq n₁ n₂ => ∃ ρ, Semantics n₁ p ρ ∧ Semantics n₂ ρ q
    | .star n => StarClosure (Semantics n) p q

/-- Notation: ⟦N⟧(σ) = set of output packets for input σ -/
def eval (N : NetKAT) (σ : Packet) : Set Packet :=
  { q : Packet | Semantics N σ q }

------------------------------------------------------------------------
-- Basic semantic identities
------------------------------------------------------------------------

/-- ⟦0⟧ = ∅ (empty relation) -/
theorem drop_empty (σ : Packet) : eval .drop σ = ∅ := by
  ext q
  constructor
  · intro h
    cases h
  · intro h
    cases h

/-- ⟦1⟧ = identity relation -/
theorem id_diag (σ τ : Packet) : Semantics .id σ τ ↔ σ = τ := by
  rfl

/-- ⟦N₁+N₂⟧ = ⟦N₁⟧ ∪ ⟦N₂⟧ -/
theorem union_sem (n₁ n₂ : NetKAT) (σ τ : Packet) :
    Semantics (n₁.union n₂) σ τ ↔ Semantics n₁ σ τ ∨ Semantics n₂ σ τ := by
  rfl

/-- ⟦N₁;N₂⟧ = ⟦N₁⟧ ∘ ⟦N₂⟧ -/
theorem seq_sem (n₁ n₂ : NetKAT) (σ τ : Packet) :
    Semantics (n₁.seq n₂) σ τ ↔ ∃ ρ, Semantics n₁ σ ρ ∧ Semantics n₂ ρ τ := by
  rfl

/-- ⟦N*⟧ contains the identity: (σ,σ) ∈ ⟦N*⟧ for all σ -/
theorem star_refl (n : NetKAT) (σ : Packet) : Semantics (n.star) σ σ :=
  StarClosure.refl σ

/-- ⟦N*⟧ is monotonic in iteration: if σ→τ via N, then σ→τ via N* -/
theorem star_step (n : NetKAT) (σ τ : Packet) :
    Semantics n σ τ → Semantics (n.star) σ τ := by
  intro h
  exact StarClosure.step h (StarClosure.refl τ)

------------------------------------------------------------------------
-- Test and assignment semantics
------------------------------------------------------------------------

/-- ⟦f=v⟧ = {(σ,σ) | σ(f) = v} — test preserves packet iff field matches -*-
    The semantics of a test is the identity relation restricted to packets
    satisfying the test predicate. -/
/- ⟦f=v⟧ = {(σ,σ) | σ(f) = v} — test preserves packet iff field matches -*-
    The semantics of a test is the identity relation restricted to packets
    satisfying the test predicate. -/
theorem fieldTest_sem (f : FieldName) (v : FieldValue) (σ τ : Packet) :
    Semantics (NetKAT.fieldTest f v) σ τ ↔ σ f = v ∧ τ = σ := by
  -- NetKAT.fieldTest f v = .test (singleton ⟨f, v⟩)
  -- Semantics .test α = (∀ fe ∈ α, σ fe.field = fe.value) ∧ σ = τ
  have test_def : NetKAT.fieldTest f v = .test (singleton (⟨f, v⟩ : FieldEq)) := by
    unfold NetKAT.fieldTest
    rfl
  rw [test_def]
  unfold Semantics
  -- Goal: (∀ fe ∈ singleton ⟨f,v⟩, σ fe.field = fe.value) ∧ σ = τ ↔ σ f = v ∧ τ = σ
  constructor
  · intro h
    cases h with
    | intro htest h_eq =>
      constructor
      · -- htest: ∀ fe ∈ singleton ⟨f,v⟩, σ fe.field = fe.value
        specialize htest (⟨f, v⟩ : FieldEq) (mem_singleton_self (⟨f, v⟩ : FieldEq))
        exact htest
      · exact h_eq.symm
  · intro h
    cases h with
    | intro h1 h2 =>
      subst h2
      constructor
      · -- Need: ∀ fe ∈ singleton ⟨f,v⟩, σ fe.field = fe.value
        intro fe hfe
        have fe_eq : fe = ⟨f, v⟩ := mem_singleton.mp hfe
        subst fe_eq
        exact h1
      · rfl

/-- ⟦f←v⟧ maps σ to σ[f↦v] — assignment updates the field -*-
    The semantics of a single-field assignment is {(σ, σ[f↦v])}.
    The assignment π = fun f' => if f = f' then v else σ f' equals
    Packet.update σ f v by definition. -/
theorem fieldAssign_sem (f : FieldName) (v : FieldValue) (σ : Packet) :
    Semantics (NetKAT.fieldAssign f v) σ (Packet.update σ f v) := by
  unfold Semantics NetKAT.fieldAssign Packet.update
  rfl

------------------------------------------------------------------------
-- Examples on concrete values
------------------------------------------------------------------------

/-- The identity relation is reflexive: every packet is related to itself. -/
theorem id_reflexive : ∀ (σ : Packet), Semantics .id σ σ := by
  intro σ
  rfl

/-- Drop produces no output packets. -/
theorem drop_no_output (σ : Packet) : eval .drop σ = ∅ := by
  exact drop_empty σ

end DyNetKAT.NetKAT
