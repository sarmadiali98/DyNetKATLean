import KATLean.Kleene
import Mathlib.Order.Hom.BoundedLattice

namespace KATLean

/-- Boolean tests embed as the subidentity, commuting idempotents of a KA.
A bounded lattice hom targets a lattice, whereas a KA only supplies joins.
The four preservation fields therefore use the KA operations directly.
Injectivity makes the test algebra a Boolean subalgebra of programs. -/
structure KAT (K B : Type*) [KleeneAlgebra K] [BooleanAlgebra B] where
  embed : B → K
  injective : Function.Injective embed
  map_bot : embed ⊥ = 0
  map_top : embed ⊤ = 1
  map_sup : ∀ a b, embed (a ⊔ b) = embed a + embed b
  map_inf : ∀ a b, embed (a ⊓ b) = embed a * embed b

namespace KAT

variable {K B : Type*} [KleeneAlgebra K] [BooleanAlgebra B] (kat : KAT K B)

theorem test_idempotent (a : B) : kat.embed a * kat.embed a = kat.embed a := by
  rw [← kat.map_inf, inf_idem]

theorem test_commute (a b : B) : kat.embed a * kat.embed b = kat.embed b * kat.embed a := by
  rw [← kat.map_inf, ← kat.map_inf, inf_comm]

theorem excluded_middle (a : B) : kat.embed a + kat.embed aᶜ = 1 := by
  rw [← kat.map_sup, sup_compl_eq_top, kat.map_top]

theorem contradiction (a : B) : kat.embed a * kat.embed aᶜ = 0 := by
  rw [← kat.map_inf, inf_compl_eq_bot, kat.map_bot]

theorem plus_one (a : B) : kat.embed a + 1 = 1 := by
  rw [← kat.map_top, ← kat.map_sup, sup_top_eq]

theorem plus_distrib (a b c : B) :
    kat.embed a + kat.embed b * kat.embed c =
      (kat.embed a + kat.embed b) * (kat.embed a + kat.embed c) := by
  rw [← kat.map_inf, ← kat.map_sup, sup_inf_left, kat.map_inf, kat.map_sup, kat.map_sup]

theorem order_iff (a b : B) : kat.embed a ≤ kat.embed b ↔ a ≤ b := by
  rw [order_iff_add, ← kat.map_sup]
  exact ⟨fun h => sup_eq_right.mp (kat.injective h),
    fun h => congrArg kat.embed (sup_eq_right.mpr h)⟩

end KAT
end KATLean
