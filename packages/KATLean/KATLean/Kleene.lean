import Mathlib.Algebra.Order.Kleene

/-! Paper-facing forms of Figure 4's KA laws, using Mathlib's classes. -/
namespace KATLean

open scoped Computability

variable {K : Type*}

theorem order_iff_add [IdemSemiring K] (a b : K) : a ≤ b ↔ a + b = b :=
  add_eq_right_iff_le.symm

variable [KleeneAlgebra K]

theorem star_induction_left {p q r : K} (h : q + p * r ≤ r) : p∗ * q ≤ r :=
  kstar_mul_le (add_le_iff.mp h).1 (add_le_iff.mp h).2

theorem star_induction_right {p q r : K} (h : p + q * r ≤ q) : p * r∗ ≤ q :=
  mul_kstar_le (add_le_iff.mp h).1 (add_le_iff.mp h).2

theorem star_induction_left_add {p q r : K} (h : (q + p * r) + r = r) :
    p∗ * q + r = r :=
  (order_iff_add _ _).mp (star_induction_left ((order_iff_add _ _).mpr h))

theorem star_induction_right_add {p q r : K} (h : (p + q * r) + q = q) :
    p * r∗ + q = q :=
  (order_iff_add _ _).mp (star_induction_right ((order_iff_add _ _).mpr h))

theorem star_unfold_left (p : K) : 1 + p * p∗ = p∗ := by
  apply le_antisymm
  · exact add_le one_le_kstar mul_kstar_le_kstar
  · have stable : p * (1 + p * p∗) ≤ 1 + p * p∗ := by
      calc
        p * (1 + p * p∗) ≤ p * p∗ := mul_le_mul_left' (add_le one_le_kstar mul_kstar_le_kstar) p
        _ ≤ 1 + p * p∗ := le_add_self
    exact kstar_le_of_mul_le_right le_self_add stable

theorem star_unfold_right (p : K) : 1 + p∗ * p = p∗ := by
  apply le_antisymm
  · exact add_le one_le_kstar kstar_mul_le_kstar
  · have stable : (1 + p∗ * p) * p ≤ 1 + p∗ * p := by
      calc
        (1 + p∗ * p) * p ≤ p∗ * p := mul_le_mul_right' (add_le one_le_kstar kstar_mul_le_kstar) p
        _ ≤ 1 + p∗ * p := le_add_self
    exact kstar_le_of_mul_le_left le_self_add stable

end KATLean
