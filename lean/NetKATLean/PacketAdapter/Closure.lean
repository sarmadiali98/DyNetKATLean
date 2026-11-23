import NetKATLean.PacketAdapter.Symbolic
import Mathlib.Data.Set.Card

/-! Reflexive-transitive closure by symbolic fixed-point iteration. The
well-founded measure is used only to prove termination. -/

namespace KATLean.NetKAT.Symbolic.Schema

open Native.Boolean
open scoped Computability

variable {F : Type} {V : F → Type} (s : Schema F V) [∀ f, DecidableEq (V f)]

/-- The encoding of an input and output packet, with a spare middle bank. -/
def encodePair (p q : (f : F) → V f) : s.Bits :=
  s.encode (fun b => if b = 0 then p else q)

theorem eval_matched {g : s.DiagramGuard} {r : Rel ((f : F) → V f)}
    (h : s.Represents g r) {v : s.Bits} {p q : (f : F) → V f}
    (hp : s.Matches 0 v p) (hq : s.Matches 1 v q) :
    eval g.1 v = true ↔ r.holds p q := by
  rw [h v]
  constructor
  · rintro ⟨p', q', hp', hq', hr⟩
    rwa [← s.matches_unique hp' hp, ← s.matches_unique hq' hq]
  · exact fun hr => ⟨p, q, hp, hq, hr⟩

theorem eval_pair {g : s.DiagramGuard} {r : Rel ((f : F) → V f)}
    (h : s.Represents g r) (p q : (f : F) → V f) :
    eval g.1 (s.encodePair p q) = true ↔ r.holds p q := by
  apply s.eval_matched h
  · simpa [encodePair] using s.matches_encode (fun b => if b = 0 then p else q) 0
  · simpa [encodePair] using s.matches_encode (fun b => if b = 0 then p else q) 1

theorem represents_unique {g : s.DiagramGuard} {r t : Rel ((f : F) → V f)}
    (hr : s.Represents g r) (ht : s.Represents g t) : r = t :=
  Rel.ext_holds (fun p q => (s.eval_pair hr p q).symm.trans (s.eval_pair ht p q))

private def square (g : s.DiagramGuard) : s.DiagramGuard := disj g (s.seq g g)

private def rejected (g : s.DiagramGuard) : Set s.Bits := {v | eval g.1 v = false}

private noncomputable def rank (g : s.DiagramGuard) : Nat := (s.rejected g).ncard

private theorem bits_finite (n : Nat) : Finite (Fin n → Bool) := by
  induction n with
  | zero =>
    apply Finite.of_injective (fun _ : Fin 0 → Bool => ())
    intro f g _
    funext i
    exact i.elim0
  | succ n ih =>
    letI := ih
    apply Finite.of_injective (fun v : Fin (n + 1) → Bool => (v 0, fun i : Fin n => v i.succ))
    intro f g h
    funext i
    refine Fin.cases (congrArg Prod.fst h) (fun j => congrFun (congrArg Prod.snd h) j) i

omit [∀ f, DecidableEq (V f)] in
private theorem rank_square_lt (g : s.DiagramGuard) (h : s.square g ≠ g) :
    s.rank (s.square g) < s.rank g := by
  letI : Finite s.Bits := bits_finite _
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  refine ⟨?_, ?_⟩
  · intro v hv
    change eval (s.square g).1 v = false at hv
    change eval g.1 v = false
    simpa [square] using (Bool.or_eq_false_iff.mp (show
      (eval g.1 v || eval (s.seq g g).1 v) = false by simpa [square] using hv)).1
  · intro sub
    apply h
    apply (guard_ext _ _).mpr
    intro v
    cases he : eval g.1 v
    · exact sub he
    · simp [square, he]

private def close (g : s.DiagramGuard) : s.DiagramGuard :=
  let next := s.square g
  if _h : next = g then g else close next
termination_by s.rank g
decreasing_by exact s.rank_square_lt g _h

private theorem close_spec (g : s.DiagramGuard) (r upper : Rel ((f : F) → V f))
    (hr : s.Represents g r) (hle : r ≤ upper) (hupper : upper * upper ≤ upper) :
    ∃ t, s.Represents (s.close g) t ∧ r ≤ t ∧ t ≤ upper ∧ t * t ≤ t := by
  induction g using (measure s.rank).wf.induction generalizing r with
  | h g ih =>
    have hsquare : s.Represents (s.square g) (r + r * r) :=
      s.union_correct hr (s.seq_correct hr hr)
    rw [close]
    split
    · rename_i he
      have eq := s.represents_unique (he ▸ hsquare) hr
      exact ⟨r, hr, le_rfl, hle, le_add_self.trans_eq eq⟩
    · rename_i he
      have hnext := add_le hle
        (((mul_le_mul_right' hle r).trans (mul_le_mul_left' hle upper)).trans hupper)
      obtain ⟨t, ht, hrt, htu, hstable⟩ :=
        ih (s.square g) (s.rank_square_lt g he) _ hsquare hnext
      exact ⟨t, ht, le_self_add.trans hrt, htu, hstable⟩

/-- Start at identity plus the body and square until the canonical diagram
is a fixed point. The executable loop never inspects the measure. -/
def star (g : s.DiagramGuard) : s.DiagramGuard := s.close (disj s.skip g)

/-- Properties preserved by a symbolic squaring round hold at the
exact closure. This applies to algebraic certificates as well as semantics. -/
theorem star_induction {g : s.DiagramGuard} {motive : s.DiagramGuard → Prop}
    (base : motive (disj s.skip g))
    (step : ∀ h, motive h → motive (disj h (s.seq h h))) :
    motive (s.star g) := by
  have loop (h : s.DiagramGuard) (hh : motive h) : motive (s.close h) := by
    induction h using (measure s.rank).wf.induction with
    | h h ih =>
      rw [close]
      split
      · exact hh
      · rename_i different
        exact ih (s.square h) (s.rank_square_lt h different) (step h hh)
  exact loop _ base

theorem star_correct {g : s.DiagramGuard} {r : Rel ((f : F) → V f)} (h : s.Represents g r) :
    s.Represents (s.star g) r∗ := by
  obtain ⟨t, ht, hstart, hupper, hstable⟩ := s.close_spec _ _ r∗
    (s.union_correct s.skip_correct h) (add_le one_le_kstar le_kstar)
    (kstar_mul_kstar r).le
  have hbelow : r∗ ≤ t := kstar_le_of_mul_le_right (le_self_add.trans hstart)
    ((mul_le_mul_right' (le_add_self.trans hstart) t).trans hstable)
  rw [le_antisymm hupper hbelow] at ht
  exact ht

end KATLean.NetKAT.Symbolic.Schema
