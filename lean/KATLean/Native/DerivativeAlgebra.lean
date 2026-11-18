import KATLean.Native.Derivatives

/-! Algebraic interpretation of the partial-derivative equations in any KAT. -/

namespace KATLean.Native

open scoped Computability

variable {T A K B : Type} [KleeneAlgebra K] [BooleanAlgebra B]
variable (kat : KAT K B) (actions : A → K) (tests : T → B)

def emptyWeight (p : Expr T A) : K :=
  kat.embed ((nullable p).interp tests)

/-- The action-consuming part of an expression's one-step equation. A right
continuation receives one argument for each partial derivative. -/
def derivativeWeight (x : Expr T A → K) : Expr T A → K
  | .zero | .one | .test _ => 0
  | .action a => actions a * x .one
  | .plus p q => derivativeWeight x p + derivativeWeight x q
  | .seq p q =>
      derivativeWeight (fun r => x (.seq r q)) p +
        emptyWeight kat tests p * derivativeWeight x q
  | .star p => derivativeWeight (fun r => x (.seq r (.star p))) p

/-- The complete one-step equation with an arbitrary right boundary value. -/
def derivativeEquation (x : Expr T A → K) (boundary : K) (p : Expr T A) : K :=
  emptyWeight kat tests p * boundary + derivativeWeight kat actions tests x p

private theorem emptyWeight_le_one (p : Expr T A) : emptyWeight kat tests p ≤ 1 := by
  rw [← kat.map_top]
  exact (kat.order_iff _ _).mpr le_top

private theorem derivativeEquation_seq (x : Expr T A → K) (boundary : K) (p q : Expr T A) :
    derivativeEquation kat actions tests x boundary (.seq p q) =
      derivativeEquation kat actions tests (fun r => x (.seq r q))
        (derivativeEquation kat actions tests x boundary q) p := by
  simp only [derivativeEquation, derivativeWeight, emptyWeight, nullable, Test.interp,
    kat.map_inf, mul_add, mul_assoc]
  simp only [add_assoc, add_comm, add_left_comm]

private theorem derivativeEquation_star (x : Expr T A → K) (boundary : K) (p : Expr T A) :
    derivativeEquation kat actions tests x boundary (.star p) =
      boundary + derivativeWeight kat actions tests (fun r => x (.seq r (.star p))) p := by
  simp [derivativeEquation, derivativeWeight, emptyWeight, nullable, Test.interp, kat.map_top]

private theorem derivativeEquation_plus (x : Expr T A → K) (boundary : K) (p q : Expr T A) :
    derivativeEquation kat actions tests x boundary (.plus p q) =
      derivativeEquation kat actions tests x boundary p +
        derivativeEquation kat actions tests x boundary q := by
  simp only [derivativeEquation, derivativeWeight, emptyWeight, nullable, Test.interp,
    kat.map_sup, add_mul]
  ac_rfl

private theorem star_of_add_below_one {d m : K} (h : d ≤ 1) : (d + m)∗ = m∗ := by
  apply le_antisymm _ (kstar_mono le_add_self)
  apply kstar_le_of_mul_le_right one_le_kstar
  rw [add_mul]
  apply add_le _ mul_kstar_le_kstar
  simpa only [one_mul] using mul_le_mul_right' h m∗

/-- Evaluating each derivative algebraically recovers the original expression
multiplied by the same right boundary. -/
theorem derivativeEquation_interp (boundary : K) (p : Expr T A) :
    derivativeEquation kat actions tests (fun r => r.interp kat actions tests * boundary) boundary p =
      p.interp kat actions tests * boundary := by
  induction p generalizing boundary with
  | zero | one | action | test =>
    simp [derivativeEquation, emptyWeight, derivativeWeight, nullable, Test.interp, Expr.interp,
      kat.map_top, kat.map_bot]
  | plus p q ihp ihq =>
    rw [derivativeEquation_plus, ihp, ihq, Expr.interp, add_mul]
  | seq p q ihp ihq =>
    rw [derivativeEquation_seq, ihq]
    simp only [Expr.interp, mul_assoc]
    exact ihp _
  | star p ih =>
    rw [derivativeEquation_star]
    simp only [Expr.interp, mul_assoc]
    have base := ih 1
    simp only [mul_one, derivativeEquation] at base
    have factor (z : K) (e : Expr T A) :
        derivativeWeight kat actions tests (fun r => r.interp kat actions tests * z) e =
          derivativeWeight kat actions tests (fun r => r.interp kat actions tests) e * z := by
      suffices ∀ (x : Expr T A → K) (e : Expr T A),
          derivativeWeight kat actions tests (fun r => x r * z) e =
            derivativeWeight kat actions tests x e * z by exact this _ _
      intro x e
      induction e generalizing x with
      | zero | one | test => simp [derivativeWeight]
      | action a => simp [derivativeWeight, mul_assoc]
      | plus a b ha hb => rw [derivativeWeight, derivativeWeight, ha, hb, add_mul]
      | seq a b ha hb => rw [derivativeWeight, derivativeWeight, ha, hb, add_mul, mul_assoc]
      | star a ha => exact ha _
    rw [factor]
    change boundary + derivativeWeight kat actions tests (fun r => r.interp kat actions tests) p *
      ((p.interp kat actions tests)∗ * boundary) = (p.interp kat actions tests)∗ * boundary
    have star_eq := star_of_add_below_one (m :=
      derivativeWeight kat actions tests (fun r => r.interp kat actions tests) p)
      (emptyWeight_le_one kat tests p)
    rw [base] at star_eq
    rw [star_eq, ← mul_assoc]
    conv_lhs => lhs; rw [← one_mul boundary]
    rw [← add_mul, star_unfold_left]

variable [DecidableEq T] [DecidableEq A]

/-- Star induction makes expression interpretation the least solution of the
partial-derivative equations. Only the structurally finite continuation set
needs to satisfy the inequalities. -/
theorem interp_le_derivativeEquation (p : Expr T A) (x : Expr T A → K) (boundary : K)
    (h : ∀ r ∈ continuations p, derivativeEquation kat actions tests x boundary r ≤ x r) :
    p.interp kat actions tests * boundary ≤ derivativeEquation kat actions tests x boundary p := by
  induction p generalizing x boundary with
  | zero | one | test =>
    simp [derivativeEquation, derivativeWeight, emptyWeight, nullable, Expr.interp, Test.interp,
      kat.map_top, kat.map_bot]
  | action a =>
    have h₁ := h .one (by simp [continuations])
    simp [derivativeEquation, derivativeWeight, emptyWeight, nullable, Expr.interp, Test.interp,
      kat.map_top, kat.map_bot] at h₁ ⊢
    exact mul_le_mul_left' h₁ _
  | plus p q ihp ihq =>
    rw [Expr.interp, add_mul, derivativeEquation_plus]
    exact add_le_add
      (ihp x boundary (fun r hr => h r (Finset.mem_union_left _ hr)))
      (ihq x boundary (fun r hr => h r (Finset.mem_union_right _ hr)))
  | seq p q ihp ihq =>
    rw [Expr.interp, mul_assoc, derivativeEquation_seq]
    apply le_trans (mul_le_mul_left' (ihq x boundary
      (fun r hr => h r (Finset.mem_union_right _ hr))) _)
    apply ihp
    intro r hr
    rw [← derivativeEquation_seq]
    exact h _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩))
  | star p ih =>
    let z := derivativeEquation kat actions tests x boundary (.star p)
    change (p.interp kat actions tests)∗ * boundary ≤ z
    have hz : z = boundary +
        derivativeWeight kat actions tests (fun r => x (.seq r (.star p))) p :=
      derivativeEquation_star kat actions tests x boundary p
    apply kstar_mul_le (by rw [hz]; exact le_self_add)
    apply le_trans (ih (fun r => x (.seq r (.star p))) z ?_)
    · rw [derivativeEquation]
      have hn : emptyWeight kat tests p * z ≤ z := by
        simpa only [one_mul] using mul_le_mul_right' (emptyWeight_le_one kat tests p) z
      exact add_le hn (hz ▸ le_add_self)
    · intro r hr
      change derivativeEquation kat actions tests _ (derivativeEquation kat actions tests x boundary
        (.star p)) r ≤ _
      rw [← derivativeEquation_seq]
      exact h _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)

end KATLean.Native
