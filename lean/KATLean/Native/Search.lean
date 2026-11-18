import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace KATLean.Native

/-- Monotone finite-set saturation, stopping immediately at a fixed point. -/
def saturate {S : Type} [DecidableEq S] (expand : Finset S → Finset S) :
    Nat → Finset S → Finset S
  | 0, visited => visited
  | n + 1, visited =>
      let next := expand visited
      if next = visited then visited else saturate expand n next

/-- The bound comes from a finite invariant carrier. No semantic verdict
uses an arbitrary search cutoff. The carrier itself is proof-only. -/
theorem saturate_closed {S : Type} [DecidableEq S] (expand : Finset S → Finset S)
    (carrier : Finset S) (grows : ∀ visited, visited ⊆ expand visited)
    (preserves : ∀ visited, visited ⊆ carrier → expand visited ⊆ carrier)
    (fuel : Nat) (visited : Finset S) (supported : visited ⊆ carrier)
    (bound : carrier.card < visited.card + fuel) :
    expand (saturate expand fuel visited) = saturate expand fuel visited := by
  induction fuel generalizing visited with
  | zero => have := Finset.card_le_card supported; omega
  | succ fuel ih =>
    simp only [saturate]
    split
    · assumption
    · rename_i different
      apply ih _ (preserves visited supported)
      have strict : visited.card < (expand visited).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨grows visited, Ne.symm different⟩)
      omega

theorem subset_saturate {S : Type} [DecidableEq S] (expand : Finset S → Finset S)
    (grows : ∀ visited, visited ⊆ expand visited) (fuel : Nat) (visited : Finset S) :
    visited ⊆ saturate expand fuel visited := by
  induction fuel generalizing visited with
  | zero => exact Finset.Subset.rfl
  | succ fuel ih =>
    simp only [saturate]
    split
    · exact Finset.Subset.rfl
    · exact (grows visited).trans (ih _)

theorem saturate_invariant {S : Type} [DecidableEq S] (expand : Finset S → Finset S)
    (Inv : Finset S → Prop) (preserves : ∀ visited, Inv visited → Inv (expand visited))
    (fuel : Nat) (visited : Finset S) (initial : Inv visited) :
    Inv (saturate expand fuel visited) := by
  induction fuel generalizing visited with
  | zero => exact initial
  | succ fuel ih =>
    simp only [saturate]
    split
    · exact initial
    · exact ih _ (preserves visited initial)

end KATLean.Native
