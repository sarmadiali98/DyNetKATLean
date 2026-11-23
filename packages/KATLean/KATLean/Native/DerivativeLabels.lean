import KATLean.Native.DerivativeAlgebra
import KATLean.Native.TestAlgebra
import KATLean.Native.FiniteSystem

/-! Finite guarded labels for the partial-derivative equations. -/

namespace KATLean.Native

open scoped BigOperators

variable {T A U K B : Type} [KleeneAlgebra K] [BooleanAlgebra B]

/-- Disjunction of the guards for a given label in a finite family. -/
def labelTest [DecidableEq U] (labels : List (Test T × U)) (u : U) : Test T :=
  labels.foldr (fun (g, v) rest => if v = u then .disj g rest else rest) .bot

theorem labelTest_eval [DecidableEq U] (labels : List (Test T × U)) (u : U) (v : Atom T) :
    (labelTest labels u).eval v = true ↔ ∃ g, (g, u) ∈ labels ∧ g.eval v = true := by
  induction labels with
  | nil => simp [labelTest, Test.eval]
  | cons pair rest ih =>
    obtain ⟨g, w⟩ := pair
    by_cases h : w = u
    · subst w
      simp only [labelTest, List.foldr_cons, ↓reduceIte, Test.eval, Bool.or_eq_true]
      change g.eval v = true ∨ (labelTest rest u).eval v = true ↔ _
      rw [ih]
      simp only [List.mem_cons, Prod.mk.injEq, and_true]
      aesop
    · simp only [labelTest, List.foldr_cons, h, if_false]
      change (labelTest rest u).eval v = true ↔ _
      rw [ih]
      simp [Ne.symm h]

theorem labelTest_sum [DecidableEq U] (kat : KAT K B) (tests : T → B)
    (labels : List (Test T × U)) (s : Finset U) (f : U → K)
    (h : ∀ label ∈ labels, label.2 ∈ s) :
    (labels.map (fun (g, u) => kat.embed (g.interp tests) * f u)).sum =
      ∑ u ∈ s, kat.embed ((labelTest labels u).interp tests) * f u := by
  induction labels with
  | nil => simp [labelTest, Test.interp, kat.map_bot]
  | cons pair rest ih =>
    obtain ⟨g, u⟩ := pair
    simp only [List.map_cons, List.sum_cons]
    rw [ih (fun e he => h e (List.mem_cons_of_mem _ he))]
    have hh : u ∈ s := h (g, u) (by simp)
    have eq (w : U) :
        kat.embed ((labelTest ((g, u) :: rest) w).interp tests) * f w =
          (if u = w then kat.embed (g.interp tests) * f w else 0) +
            kat.embed ((labelTest rest w).interp tests) * f w := by
      by_cases same : u = w <;> simp [labelTest, same, Test.interp, kat.map_sup, add_mul]
    simp only [eq, Finset.sum_add_distrib]
    congr 1
    simp [hh, eq_comm (a := u)]

/-- The syntactic first steps carry a Boolean guard, primitive action and
continuation. This proof representation uses finite syntax only. -/
def derivativeLabels : Expr T A → List (Test T × (A × Expr T A))
  | .zero | .one | .test _ => []
  | .action a => [(.top, a, .one)]
  | .plus p q => derivativeLabels p ++ derivativeLabels q
  | .seq p q =>
    (derivativeLabels p).map (fun (g, a, r) => (g, a, .seq r q)) ++
      (derivativeLabels q).map (fun (g, a, r) => (.conj (nullable p) g, a, r))
  | .star p => (derivativeLabels p).map (fun (g, a, r) => (g, a, .seq r (.star p)))

theorem derivativeLabels_support [DecidableEq T] [DecidableEq A] (p : Expr T A)
    (e : Test T × (A × Expr T A)) (h : e ∈ derivativeLabels p) :
    e.2.2 ∈ continuations p := by
  induction p generalizing e with
  | zero | one | test => simp [derivativeLabels] at h
  | action a =>
    obtain rfl := List.mem_singleton.mp h
    simp [continuations]
  | plus p q hp hq =>
    exact (List.mem_append.mp h).elim
      (fun h => Finset.mem_union_left _ (hp _ h)) (fun h => Finset.mem_union_right _ (hq _ h))
  | seq p q hp hq =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r.2.2, hp _ hr, rfl⟩)
    · obtain ⟨⟨g, a, r⟩, hr, rfl⟩ := List.mem_map.mp h
      exact Finset.mem_union_right _ (hq (g, a, r) hr)
  | star p hp =>
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    exact Finset.mem_image.mpr ⟨r.2.2, hp _ hr, rfl⟩

theorem derivativeLabels_correct [DecidableEq T] [DecidableEq A] (p : Expr T A)
    (v : Atom T) (a : A) (r : Expr T A) :
    (labelTest (derivativeLabels p) (a, r)).eval v = true ↔ r ∈ derivative p v a := by
  simp only [labelTest_eval]
  induction p generalizing r with
  | zero | one | test => simp [derivativeLabels, derivative]
  | action b =>
    by_cases same : b = a
    · subst b
      rw [derivative, if_pos rfl]
      simp only [derivativeLabels, List.mem_singleton, Prod.mk.injEq, Finset.mem_singleton, true_and]
      exact ⟨fun ⟨_, ⟨_, h⟩, _⟩ => h, fun h => ⟨.top, ⟨rfl, h⟩, rfl⟩⟩
    · simp [derivativeLabels, derivative, same, Ne.symm same]
  | plus p q hp hq =>
    rw [derivative, Finset.mem_union, ← hp, ← hq]
    simp only [derivativeLabels, List.mem_append]
    exact ⟨fun ⟨g, h, hg⟩ => h.elim (fun h => Or.inl ⟨g, h, hg⟩)
      (fun h => Or.inr ⟨g, h, hg⟩),
      fun h => h.elim (fun ⟨g, h, hg⟩ => ⟨g, Or.inl h, hg⟩)
        (fun ⟨g, h, hg⟩ => ⟨g, Or.inr h, hg⟩)⟩
  | seq p q hp hq =>
    rw [derivative, Finset.mem_union]
    constructor
    · rintro ⟨g, h, hg⟩
      rcases List.mem_append.mp h with h | h
      · obtain ⟨⟨g', a', r'⟩, hm, he⟩ := List.mem_map.mp h
        cases he
        exact Or.inl (Finset.mem_image.mpr ⟨r', (hp _).mp ⟨g, hm, hg⟩, rfl⟩)
      · obtain ⟨⟨g', a', r'⟩, hm, he⟩ := List.mem_map.mp h
        cases he
        obtain ⟨hn, hg'⟩ := (Bool.and_eq_true _ _).mp hg
        exact Or.inr (by simpa only [hn, if_true] using (hq _).mp ⟨g', hm, hg'⟩)
    · rintro (h | h)
      · obtain ⟨r', hm, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨g, hg, he⟩ := (hp _).mpr hm
        exact ⟨g, List.mem_append_left _ (List.mem_map.mpr ⟨(g, a, r'), hg, rfl⟩), he⟩
      · by_cases hn : (nullable p).eval v = true
        · rw [if_pos hn] at h
          obtain ⟨g, hg, he⟩ := (hq _).mpr h
          exact ⟨.conj (nullable p) g, List.mem_append_right _
            (List.mem_map.mpr ⟨(g, a, r), hg, rfl⟩), (Bool.and_eq_true _ _).mpr ⟨hn, he⟩⟩
        · simp [hn] at h
  | star p hp =>
    rw [derivative, Finset.mem_image]
    constructor
    · rintro ⟨g, h, hg⟩
      obtain ⟨⟨g', a', r'⟩, hm, he⟩ := List.mem_map.mp h
      cases he
      exact ⟨r', (hp _).mp ⟨g, hm, hg⟩, rfl⟩
    · rintro ⟨r', h, rfl⟩
      obtain ⟨g, hg, he⟩ := (hp _).mpr h
      exact ⟨g, List.mem_map.mpr ⟨(g, a, r'), hg, rfl⟩, he⟩

private theorem list_sum_mul_left (x : K) (l : List K) :
    (l.map (x * ·)).sum = x * l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

theorem derivativeLabels_weight (kat : KAT K B) (actions : A → K) (tests : T → B)
    (x : Expr T A → K) (p : Expr T A) :
    ((derivativeLabels p).map (fun (g, a, r) => kat.embed (g.interp tests) * (actions a * x r))).sum =
      derivativeWeight kat actions tests x p := by
  induction p generalizing x with
  | zero | one | test => rfl
  | action a => simp [derivativeLabels, derivativeWeight, Test.interp, kat.map_top]
  | plus p q hp hq =>
    simp only [derivativeLabels, derivativeWeight, List.map_append, List.sum_append, hp, hq]
  | seq p q hp hq =>
    simp only [derivativeLabels, derivativeWeight, List.map_append, List.sum_append, List.map_map]
    rw [← hp, ← hq, ← list_sum_mul_left, List.map_map]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    rintro ⟨g, a, r⟩ _
    change kat.embed ((Test.conj (nullable p) g).interp tests) * (actions a * x r) =
      kat.embed ((nullable p).interp tests) * (kat.embed (g.interp tests) * (actions a * x r))
    rw [Test.interp, kat.map_inf, mul_assoc]
  | star p hp =>
    simp only [derivativeLabels, derivativeWeight, List.map_map]
    rw [← hp]
    apply congrArg List.sum
    apply List.map_congr_left
    rintro ⟨g, a, r⟩ _
    rfl

end KATLean.Native
