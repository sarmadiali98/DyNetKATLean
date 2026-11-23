import KATLean.Kleene
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite affine systems over an arbitrary Kleene algebra, solved by eliminating
  one variable at a time. The least-solution result uses star induction. -/

namespace KATLean.Native.FiniteSystem

open scoped BigOperators Computability

variable {K : Type*} [KleeneAlgebra K]
variable {ι : Type*} [Fintype ι]

/-- The affine operator with coefficients `m` and boundary vector `b`. -/
def affine (m : ι → ι → K) (b x : ι → K) (i : ι) : K :=
  b i + ∑ j, m i j * x j

/-- An upper solution satisfies every affine inequality. -/
def UpperSolution (m : ι → ι → K) (b x : ι → K) : Prop :=
  ∀ i, affine m b x i ≤ x i

private theorem affine_succ {n : Nat} (m : Fin (n + 1) → Fin (n + 1) → K)
    (b x : Fin (n + 1) → K) (i : Fin (n + 1)) :
    affine m b x i = b i + m i 0 * x 0 + ∑ j : Fin n, m i j.succ * x j.succ := by
  rw [affine, Fin.sum_univ_succ, add_assoc]

private def reducedMatrix {n : Nat} (m : Fin (n + 1) → Fin (n + 1) → K)
    (i j : Fin n) : K := m i.succ j.succ + m i.succ 0 * (m 0 0)∗ * m 0 j.succ

private def reducedBoundary {n : Nat} (m : Fin (n + 1) → Fin (n + 1) → K)
    (b : Fin (n + 1) → K) (i : Fin n) : K := b i.succ + m i.succ 0 * (m 0 0)∗ * b 0

private def solveFin : (n : Nat) → (Fin n → Fin n → K) → (Fin n → K) → Fin n → K
  | 0, _, _ => Fin.elim0
  | n + 1, m, b =>
    let tail := solveFin n (reducedMatrix m) (reducedBoundary m b)
    Fin.cases ((m 0 0)∗ * (b 0 + ∑ j : Fin n, m 0 j.succ * tail j)) tail

private theorem solve_fin (n : Nat) (m : Fin n → Fin n → K) (b : Fin n → K) :
    (∀ i, affine m b (solveFin n m b) i = solveFin n m b i) ∧
      ∀ x, UpperSolution m b x → ∀ i, solveFin n m b i ≤ x i := by
  induction n with
  | zero => exact ⟨fun i => i.elim0, fun _ _ i => i.elim0⟩
  | succ n ih =>
    let loop := (m 0 0)∗
    let head (x : Fin n → K) := loop * (b 0 + ∑ j, m 0 j.succ * x j)
    let m' := reducedMatrix m
    let b' := reducedBoundary m b
    have head_eq (x : Fin n → K) :
        b 0 + m 0 0 * head x + ∑ j, m 0 j.succ * x j = head x := by
      unfold head loop
      rw [← add_right_comm, ← mul_assoc]
      conv_lhs => lhs; rw [← one_mul (b 0 + ∑ j, m 0 j.succ * x j)]
      rw [← add_mul, star_unfold_left]
    have tail_eq (x : Fin n → K) (i : Fin n) :
        affine m' b' x i = b i.succ + m i.succ 0 * head x + ∑ j, m i.succ j.succ * x j := by
      simp only [affine, m', b', reducedMatrix, reducedBoundary, head, loop, add_mul, mul_add, ← mul_assoc, Finset.sum_add_distrib,
        Finset.mul_sum]
      ac_rfl
    let y := solveFin n m' b'
    obtain ⟨hFixed, hLeast⟩ := ih m' b'
    change (∀ i, affine m b (Fin.cases (head y) y) i = Fin.cases (head y) y i) ∧ _
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [affine_succ]
        exact head_eq y
      · rw [affine_succ]
        change b j.succ + m j.succ 0 * head y + ∑ k, m j.succ k.succ * y k = y j
        rw [← tail_eq]
        exact hFixed j
    · intro x hx
      let tail (i : Fin n) := x i.succ
      have hh : head tail ≤ x 0 := by
        apply KATLean.star_induction_left
        have h := hx 0
        rw [affine_succ, add_right_comm] at h
        exact h
      have ht : UpperSolution m' b' tail := by
        intro i
        rw [tail_eq]
        exact (add_le_add_right (add_le_add_left (mul_le_mul_left' hh _) _) _).trans
          ((affine_succ m b x i.succ) ▸ hx i.succ)
      have hy : ∀ i, y i ≤ tail i := hLeast tail ht
      intro i
      change Fin.cases (head y) y i ≤ x i
      refine Fin.cases ?_ (fun j => hy j) i
      exact (mul_le_mul_left'
        (add_le_add_left (Finset.sum_le_sum (fun j _ => mul_le_mul_left' (hy j) _)) _) _).trans hh

private theorem solveFin_add (n : Nat) (m : Fin n → Fin n → K) (b c : Fin n → K) :
    solveFin n m (b + c) = solveFin n m b + solveFin n m c := by
  induction n with
  | zero => ext i; exact i.elim0
  | succ n ih =>
    have hb : reducedBoundary m (b + c) = reducedBoundary m b + reducedBoundary m c := by
      ext i
      simp only [reducedBoundary, Pi.add_apply, mul_add]
      ac_rfl
    have htail := ih (reducedMatrix m) (reducedBoundary m b) (reducedBoundary m c)
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [solveFin, Pi.add_apply, Fin.cases_zero, hb, htail, mul_add,
        Finset.sum_add_distrib]
      ac_rfl
    · simp only [solveFin, Fin.cases_succ, hb, htail, Pi.add_apply]

private theorem solveFin_mul (n : Nat) (m : Fin n → Fin n → K) (b : Fin n → K) (c : K) :
    solveFin n m (fun i => b i * c) = fun i => solveFin n m b i * c := by
  induction n with
  | zero => ext i; exact i.elim0
  | succ n ih =>
    have hb : reducedBoundary m (fun i => b i * c) = fun i => reducedBoundary m b i * c := by
      ext i
      simp only [reducedBoundary, add_mul, mul_assoc]
    have htail := ih (reducedMatrix m) (reducedBoundary m b)
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [solveFin, Fin.cases_zero, hb, htail, add_mul, Finset.sum_mul, mul_assoc]
    · simp [solveFin, hb, htail]

/-- Least upper solution defined by finite elimination. -/
noncomputable def solve (m : ι → ι → K) (b : ι → K) (i : ι) : K :=
  let e := Fintype.equivFin ι
  solveFin _ (fun i j => m (e.symm i) (e.symm j)) (fun i => b (e.symm i)) (e i)

theorem solve_add (m : ι → ι → K) (b c : ι → K) :
    solve m (b + c) = solve m b + solve m c := by
  ext i
  let e := Fintype.equivFin ι
  exact congrFun (solveFin_add _ (fun j k => m (e.symm j) (e.symm k))
    (fun j => b (e.symm j)) (fun j => c (e.symm j))) (e i)

theorem solve_mul (m : ι → ι → K) (b : ι → K) (c : K) :
    solve m (fun i => b i * c) = fun i => solve m b i * c := by
  ext i
  simp only [solve, solveFin_mul]

/-- A finite affine system has a least upper solution, which is a fixed point. -/
theorem solve_spec (m : ι → ι → K) (b : ι → K) :
    (∀ i, affine m b (solve m b) i = solve m b i) ∧
      ∀ x, UpperSolution m b x → ∀ i, solve m b i ≤ x i := by
  let e := Fintype.equivFin ι
  let m' := fun i j => m (e.symm i) (e.symm j)
  let b' := fun i => b (e.symm i)
  let y := solveFin _ m' b'
  obtain ⟨hFixed, hLeast⟩ := solve_fin _ m' b'
  have reindex (x : ι → K) (i) :
      affine (fun i j => m (e.symm i) (e.symm j)) (fun i => b (e.symm i))
        (fun i => x (e.symm i)) i = affine m b x (e.symm i) := by
    unfold affine
    congr 1
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  change (∀ i, affine m b (fun j => y (e j)) i = y (e i)) ∧ _
  refine ⟨?_, ?_⟩
  · intro i
    have h := reindex (fun i => y (e i)) (e i)
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at h
    exact h.symm.trans (hFixed (e i))
  · intro x hx i
    apply hLeast (fun j => x (e.symm j)) _ (e i) |>.trans_eq (congrArg x (e.symm_apply_apply i))
    intro j
    rw [reindex]
    exact hx _

end KATLean.Native.FiniteSystem
