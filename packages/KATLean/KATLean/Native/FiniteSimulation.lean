import KATLean.Native.FiniteSystem
import Mathlib.Algebra.Ring.Opposite

/-! Weighted simulation over finite systems. Rectangular multiplication lets
a simulation transfer least solutions between different index types. -/

namespace KATLean.Native.FiniteSystem

open scoped BigOperators Computability
open MulOpposite

variable {K : Type*} [KleeneAlgebra K]
variable {I J L M : Type*}

private instance : IdemSemiring Kᵐᵒᵖ :=
  IdemSemiring.ofSemiring (fun _ => unop_injective (add_idem _))

private instance : KleeneAlgebra Kᵐᵒᵖ where
  kstar a := op (a.unop)∗
  one_le_kstar _ := (order_iff_add _ _).mpr (unop_injective ((order_iff_add _ _).mp one_le_kstar))
  mul_kstar_le_kstar _ := (order_iff_add _ _).mpr
    (unop_injective ((order_iff_add _ _).mp kstar_mul_le_kstar))
  kstar_mul_le_kstar _ := (order_iff_add _ _).mpr
    (unop_injective ((order_iff_add _ _).mp mul_kstar_le_kstar))
  mul_kstar_le_self _ _ h := (order_iff_add _ _).mpr
    (unop_injective ((order_iff_add _ _).mp
      (kstar_mul_le_self (congrArg unop ((order_iff_add _ _).mp h) |> add_eq_right_iff_le.mp))))
  kstar_mul_le_self _ _ h := (order_iff_add _ _).mpr
    (unop_injective ((order_iff_add _ _).mp
      (mul_kstar_le_self (congrArg unop ((order_iff_add _ _).mp h) |> add_eq_right_iff_le.mp))))

/-- Rectangular matrix multiplication over the coefficient algebra. -/
def mul [Fintype J] (a : I → J → K) (b : J → L → K) : I → L → K :=
  fun i k => ∑ j, a i j * b j k

local infixl:70 " ⬝ " => mul

private theorem mul_assoc' [Fintype J] [Fintype L]
    (a : I → J → K) (b : J → L → K) (c : L → M → K) :
    (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c) := by
  funext i k
  simp only [mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private theorem mul_le [Fintype J] {a a' : I → J → K} {b b' : J → L → K}
    (ha : a ≤ a') (hb : b ≤ b') : a ⬝ b ≤ a' ⬝ b' :=
  fun i k => Finset.sum_le_sum (fun j _ => (mul_le_mul_right' (ha i j) _).trans
    (mul_le_mul_left' (hb j k) _))

private def unit [DecidableEq I] (i j : I) : K := if i = j then 1 else 0

private theorem unit_mul [Fintype I] [DecidableEq I] (a : I → J → K) :
    unit ⬝ a = a := by
  funext i j
  simp [mul, unit, ite_mul, eq_comm]

private theorem mul_unit [Fintype J] [DecidableEq J] (a : I → J → K) :
    a ⬝ unit = a := by
  funext i j
  simp [mul, unit, mul_ite]

private noncomputable def closure [Fintype I] [DecidableEq I] (m : I → I → K) (i j : I) : K :=
  solve m (fun k => unit k j) i

private theorem solve_sum [Fintype I] (m : I → I → K) (s : Finset J) (b : J → I → K) :
    solve m (∑ j ∈ s, b j) = ∑ j ∈ s, solve m (b j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : UpperSolution m 0 0 := by intro i; simp [affine]
    have hz := (solve_spec m 0).2 0 h
    simpa only [Finset.sum_empty] using funext (fun i => (hz i).antisymm (zero_le _))
  | insert j s h ih => rw [Finset.sum_insert h, Finset.sum_insert h, solve_add, ih]

private theorem sum_apply (s : Finset J) (f : J → I → K) (i : I) :
    (∑ j ∈ s, f j) i = ∑ j ∈ s, f j i := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert j s h ih => rw [Finset.sum_insert h, Finset.sum_insert h, Pi.add_apply, ih]

private theorem solve_eq_sum [Fintype I] [DecidableEq I] (m : I → I → K) (b : I → K) (i : I) :
    solve m b i = ∑ j, closure m i j * b j := by
  have h : b = ∑ j, fun k => unit k j * b j := by
    funext k
    simp [sum_apply, unit, ite_mul, eq_comm]
  conv_lhs => rw [h, solve_sum]
  simp only [sum_apply, solve_mul, closure]

private theorem left_spec [Fintype I] [DecidableEq I] (m : I → I → K) (b : I → J → K) :
    b + m ⬝ (closure m ⬝ b) = closure m ⬝ b ∧
      ∀ x, b + m ⬝ x ≤ x → closure m ⬝ b ≤ x := by
  constructor
  · funext i j
    simpa only [affine, solve_eq_sum] using (solve_spec m (fun i => b i j)).1 i
  · intro x h i j
    simpa only [solve_eq_sum] using (solve_spec m (fun i => b i j)).2 (fun i => x i j)
      (fun k => h k j) i

private def transposeOp (a : I → J → K) : J → I → Kᵐᵒᵖ := fun j i => op (a i j)

private theorem transpose_mul [Fintype J] (a : I → J → K) (b : J → L → K) :
    transposeOp (a ⬝ b) = transposeOp b ⬝ transposeOp a := by
  funext k i
  exact map_sum (MulOpposite.opAddEquiv : K ≃+ Kᵐᵒᵖ) _ _

private theorem transpose_le {a b : I → J → K} :
    transposeOp a ≤ transposeOp b ↔ a ≤ b := by
  constructor
  · intro h i j
    exact add_eq_right_iff_le.mp (congrArg unop (add_eq_right_iff_le.mpr (h j i)))
  · intro h j i
    exact add_eq_right_iff_le.mp (congrArg op (add_eq_right_iff_le.mpr (h i j)))

private noncomputable def rightClosure [Fintype I] [DecidableEq I] (m : I → I → K) :
    I → I → K := fun i j => unop (closure (transposeOp m) j i)

private theorem right_spec [Fintype I] [DecidableEq I] (m : I → I → K) (b : J → I → K) :
    b + (b ⬝ rightClosure m) ⬝ m = b ⬝ rightClosure m ∧
      ∀ x, b + x ⬝ m ≤ x → b ⬝ rightClosure m ≤ x := by
  obtain ⟨hf, hl⟩ := left_spec (transposeOp m) (transposeOp b)
  have hr : transposeOp (rightClosure m) = closure (transposeOp m) := rfl
  constructor
  · have h : transposeOp (b + (b ⬝ rightClosure m) ⬝ m) =
        transposeOp (b ⬝ rightClosure m) := by
      change transposeOp b + transposeOp ((b ⬝ rightClosure m) ⬝ m) = _
      simpa only [transpose_mul, hr] using hf
    exact le_antisymm (transpose_le.mp h.le) (transpose_le.mp h.ge)
  · intro x h
    apply transpose_le.mp
    rw [transpose_mul, hr]
    apply hl
    have hx := transpose_le.mpr h
    change transposeOp b + transposeOp (x ⬝ m) ≤ transposeOp x at hx
    rwa [transpose_mul] at hx

private theorem closure_eq_right [Fintype I] [DecidableEq I] (m : I → I → K) :
    closure m = rightClosure m := by
  obtain ⟨hl, hll⟩ := left_spec m (unit : I → I → K)
  obtain ⟨hr, hrl⟩ := right_spec m (unit : I → I → K)
  rw [mul_unit] at hl hll
  rw [unit_mul] at hr hrl
  have huL : (unit : I → I → K) ≤ closure m := fun i j =>
    le_self_add.trans_eq (congrFun (congrFun hl i) j)
  have huR : (unit : I → I → K) ≤ rightClosure m := fun i j =>
    le_self_add.trans_eq (congrFun (congrFun hr i) j)
  have hL : m ⬝ closure m ≤ closure m := fun i j =>
    le_add_self.trans_eq (congrFun (congrFun hl i) j)
  have hR : rightClosure m ⬝ m ≤ rightClosure m := fun i j =>
    le_add_self.trans_eq (congrFun (congrFun hr i) j)
  have hmL : m ≤ closure m := (by rw [mul_unit] : m ≤ m ⬝ unit).trans
    ((mul_le le_rfl huL).trans hL)
  have hmR : m ≤ rightClosure m := (by rw [unit_mul] : m ≤ unit ⬝ m).trans
    ((mul_le huR le_rfl).trans hR)
  have hLm : closure m ⬝ m ≤ closure m :=
    (left_spec m m).2 _ (fun i j => add_le (hmL i j) (hL i j))
  have hmR' : m ⬝ rightClosure m ≤ rightClosure m :=
    (right_spec m m).2 _ (fun i j => add_le (hmR i j) (hR i j))
  exact le_antisymm (hll _ (fun i j => add_le (huR i j) (hmR' i j)))
    (hrl _ (fun i j => add_le (huL i j) (hLm i j)))

/-- A rectangular intertwiner transports the closures of the two systems.
Both star-induction directions enter via the least upper solution properties. -/
theorem closure_intertwines [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (m : I → I → K) (n : J → J → K) (x : I → J → K)
    (h : m ⬝ x = x ⬝ n) : closure m ⬝ x = x ⬝ closure n := by
  have e₁ := (left_spec n (unit : J → J → K)).1
  have e₂ := (right_spec m (unit : I → I → K)).1
  rw [mul_unit] at e₁
  rw [unit_mul, ← closure_eq_right] at e₂
  apply le_antisymm
  · apply (left_spec m x).2
    have hu : (unit : J → J → K) ≤ closure n := fun i j =>
      le_self_add.trans_eq (congrFun (congrFun e₁ i) j)
    have hn : n ⬝ closure n ≤ closure n := fun i j =>
      le_add_self.trans_eq (congrFun (congrFun e₁ i) j)
    rw [← mul_assoc', h, mul_assoc']
    exact fun i j => add_le
      (((mul_unit x).symm.le.trans (mul_le le_rfl hu)) i j) (mul_le le_rfl hn i j)
  · rw [closure_eq_right n]
    apply (right_spec n x).2
    have hu : (unit : I → I → K) ≤ closure m := fun i j =>
      le_self_add.trans_eq (congrFun (congrFun e₂ i) j)
    have hm : closure m ⬝ m ≤ closure m := fun i j =>
      le_add_self.trans_eq (congrFun (congrFun e₂ i) j)
    rw [mul_assoc', ← h, ← mul_assoc']
    exact fun i j => add_le
      (((unit_mul x).symm.le.trans (mul_le hu le_rfl)) i j) (mul_le hm le_rfl i j)

/-- If a rectangular intertwiner also maps the boundary of one system to the
other, it maps their least solutions. -/
theorem solve_intertwines [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (m : I → I → K) (n : J → J → K) (x : I → J → K) (b : J → K)
    (h : m ⬝ x = x ⬝ n) :
    solve m (fun i => ∑ j, x i j * b j) = fun i => ∑ j, x i j * solve n b j := by
  let c : J → Unit → K := fun j _ => b j
  have eq : closure m ⬝ (x ⬝ c) = x ⬝ (closure n ⬝ c) := by
    rw [← mul_assoc', closure_intertwines m n x h, mul_assoc']
  funext i
  simpa only [mul, c, ← solve_eq_sum] using congrFun (congrFun eq i) ()

end KATLean.Native.FiniteSystem
