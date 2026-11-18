import KATLean.Native.Boolean
import Mathlib.Order.PrimeSeparator

/-! Boolean truth in symbolic guards reflects order in every Boolean algebra.
Prime ideals are used only in proofs. -/

namespace KATLean.Native

open Order

private theorem eval_prime_ideal {T B : Type} [BooleanAlgebra B]
    (v : T → B) (I : Ideal B) (prime : I.IsPrime) (p : Test T) :
    letI := Classical.decPred (fun b : B => b ∉ I)
    p.eval (fun t => decide (v t ∉ I)) = true ↔ p.interp v ∉ I := by
  classical
  letI : ∀ b : B, Decidable (b ∉ I) := Classical.decPred _
  change p.eval (fun t => decide (v t ∉ I)) = true ↔ p.interp v ∉ I
  induction p with
  | bot => simp [Test.interp, Test.eval, I.bot_mem]
  | top => simp [Test.interp, Test.eval, prime.toIsProper.top_not_mem]
  | atom => simp [Test.interp, Test.eval]
  | conj p q hp hq =>
    rw [Test.interp, Test.eval, Bool.and_eq_true, hp, hq]
    exact ⟨fun h hmem => (prime.mem_or_mem hmem).elim h.1 h.2,
      fun h => ⟨fun hmem => h (I.lower inf_le_left hmem),
        fun hmem => h (I.lower inf_le_right hmem)⟩⟩
  | disj p q hp hq =>
    rw [Test.interp, Test.eval, Bool.or_eq_true, hp, hq]
    exact ⟨fun h hmem => h.elim (fun hn => hn (I.lower le_sup_left hmem))
      (fun hn => hn (I.lower le_sup_right hmem)),
      fun h => by
        by_cases hmem : p.interp v ∈ I
        · exact Or.inr (fun hq => h (Ideal.sup_mem hmem hq))
        · exact Or.inl hmem⟩
  | neg p hp =>
    rw [Test.interp, Test.eval, Bool.not_eq_true', ← Bool.not_eq_true, hp, not_not]
    exact ⟨fun h hcomp => prime.toIsProper.top_not_mem
      ((sup_compl_eq_top (x := p.interp v)) ▸ Ideal.sup_mem h hcomp),
      fun h => by
        by_cases hx : p.interp v ∈ I
        · exact hx
        · exact (h (prime.mem_compl_of_not_mem hx)).elim⟩

/-- A truth implication between Boolean tests holds in every Boolean algebra. -/
theorem Test.interp_le_of_eval {T B : Type} [BooleanAlgebra B] (p q : Test T) (v : T → B)
    (h : ∀ w, p.eval w = true → q.eval w = true) : p.interp v ≤ q.interp v := by
  classical
  by_contra hle
  have hd : Disjoint (PFilter.principal (p.interp v) : Set B)
      (Ideal.principal (q.interp v) : Set B) :=
    Set.disjoint_left.mpr (fun _ hp hq =>
      hle ((PFilter.mem_principal.mp hp).trans (Ideal.mem_principal.mp hq)))
  obtain ⟨I, hPrime, hIncl, hDisj⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hd
  have hp : p.interp v ∉ I := Set.disjoint_left.mp hDisj
    (PFilter.mem_principal.mpr le_rfl)
  have hq : q.interp v ∈ I := hIncl Ideal.mem_principal_self
  exact ((eval_prime_ideal v I hPrime q).mp
    (h _ ((eval_prime_ideal v I hPrime p).mpr hp))) hq

/-- Tests with the same truth function agree under every Boolean interpretation. -/
theorem Test.interp_eq_of_eval {T B : Type} [BooleanAlgebra B] (p q : Test T) (v : T → B)
    (h : ∀ w, p.eval w = q.eval w) : p.interp v = q.interp v :=
  le_antisymm (p.interp_le_of_eval q v (fun w hw => h w ▸ hw))
    (q.interp_le_of_eval p v (fun w hw => (h w).symm ▸ hw))

namespace Boolean

/-- Read a symbolic tree as a Boolean formula using its variable numbering. -/
def Diagram.toTest {T : Type} : (d : Diagram n) → (Fin n → T) → Test T
  | .leaf false, _ => .bot
  | .leaf true, _ => .top
  | .skip d, t => toTest d (fun i => t i.succ)
  | .node l r, t =>
    .disj (.conj (.neg (.atom (t 0))) (toTest l (fun i => t i.succ)))
      (.conj (.atom (t 0)) (toTest r (fun i => t i.succ)))

theorem Diagram.toTest_correct {T : Type} (d : Diagram n) (t : Fin n → T) (v : T → Bool) :
    (d.toTest t).eval v = eval d (fun i => v (t i)) := by
  induction d with
  | leaf b => cases b <;> rfl
  | skip d ih => exact ih _
  | node l r ihl ihr =>
    simp only [Diagram.toTest, Test.eval, eval, ihl, ihr]
    cases v (t 0) <;> simp

end Boolean
end KATLean.Native
