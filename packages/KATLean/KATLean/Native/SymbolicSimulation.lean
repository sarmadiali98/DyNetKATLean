import KATLean.Native.DerivativeLabels
import KATLean.Native.FiniteSimulation
import KATLean.Native.Decision

/-! Lifting Boolean-labelled simulations to the finite systems used in the
algebraic completeness proof. -/

namespace KATLean.Native

open scoped BigOperators
open FiniteSystem

variable {T A K B : Type} [KleeneAlgebra K] [BooleanAlgebra B]

private noncomputable def testDisjunction {I : Type} (s : Finset I) (f : I → Test T) : Test T :=
  (s.toList.map f).foldr Test.disj .bot

private theorem list_disjunction_eval (s : List (Test T)) (v : Atom T) :
    (s.foldr Test.disj .bot).eval v = true ↔ ∃ g ∈ s, g.eval v = true := by
  induction s with
  | nil => simp [Test.eval]
  | cons g rest ih =>
    simp only [List.foldr_cons, Test.eval, Bool.or_eq_true, ih, List.mem_cons]
    aesop

private theorem testDisjunction_eval {I : Type} (s : Finset I) (f : I → Test T) (v : Atom T) :
    (testDisjunction s f).eval v = true ↔ ∃ i ∈ s, (f i).eval v = true := by
  simp only [testDisjunction, list_disjunction_eval, List.mem_map, Finset.mem_toList]
  aesop

private theorem embed_testDisjunction {I : Type} (kat : KAT K B) (tests : T → B)
    (s : Finset I) (f : I → Test T) :
    kat.embed ((testDisjunction s f).interp tests) = ∑ i ∈ s, kat.embed ((f i).interp tests) := by
  have h (l : List I) :
      kat.embed (((l.map f).foldr Test.disj .bot).interp tests) =
        (l.map (fun i => kat.embed ((f i).interp tests))).sum := by
    induction l with
    | nil => simp [Test.interp, kat.map_bot]
    | cons i l ih => simp only [List.map_cons, List.foldr_cons, Test.interp, kat.map_sup, List.sum_cons, ih]
  rw [testDisjunction, h]
  exact Finset.sum_map_toList _ _

private def weighted (kat : KAT K B) (actions : A → K) (tests : T → B) [Fintype A]
    {I J : Type} (g : I → A → J → Test T) (i : I) (j : J) : K :=
  ∑ a, kat.embed ((g i a j).interp tests) * actions a

private noncomputable def incidence {I J : Type} (r : I → J → Prop) (i : I) (j : J) : K :=
  open Classical in if r i j then 1 else 0

private theorem weighted_intertwines {I J : Type} [Fintype I] [Fintype J] [Fintype A]
    (kat : KAT K B) (actions : A → K) (tests : T → B)
    (m : I → A → I → Test T) (n : J → A → J → Test T) (r : I → J → Prop)
    (h : ∀ i a j v, (∃ k, r k j ∧ (m i a k).eval v = true) ↔
      ∃ k, r i k ∧ (n k a j).eval v = true) :
    mul (weighted kat actions tests m) (incidence r) =
      mul (incidence r) (weighted kat actions tests n) := by
  classical
  funext i j
  simp only [mul, weighted, incidence]
  have left (k : I) :
      (∑ a, kat.embed ((m i a k).interp tests) * actions a) * (if r k j then 1 else 0) =
        ∑ a, (if r k j then kat.embed ((m i a k).interp tests) * actions a else 0) := by
    by_cases hr : r k j <;> simp [hr]
  have right (k : J) :
      (if r i k then 1 else 0) * (∑ a, kat.embed ((n k a j).interp tests) * actions a) =
        ∑ a, (if r i k then kat.embed ((n k a j).interp tests) * actions a else 0) := by
    by_cases hr : r i k <;> simp [hr]
  simp only [left, right]
  rw [Finset.sum_comm (s := (Finset.univ : Finset I)), Finset.sum_comm (s := (Finset.univ : Finset J))]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_mul, ← Finset.sum_mul,
    ← embed_testDisjunction, ← embed_testDisjunction]
  congr 2
  apply Test.interp_eq_of_eval
  intro v
  apply Bool.eq_iff_iff.mpr
  simpa only [testDisjunction_eval, Finset.mem_filter, Finset.mem_univ, true_and] using h i a j v

private theorem output_intertwines {I J : Type} [Fintype J]
    (kat : KAT K B) (tests : T → B) (b : I → Test T) (c : J → Test T) (r : I → J → Prop)
    (h : ∀ i v, (b i).eval v = true ↔ ∃ j, r i j ∧ (c j).eval v = true) (i : I) :
    kat.embed ((b i).interp tests) = ∑ j, incidence (K := K) r i j * kat.embed ((c j).interp tests) := by
  classical
  have eq (j : J) :
      incidence (K := K) r i j * kat.embed ((c j).interp tests) =
        if r i j then kat.embed ((c j).interp tests) else 0 := by
    by_cases hr : r i j <;> simp [incidence, hr]
  simp only [eq]
  rw [← Finset.sum_filter, ← embed_testDisjunction]
  congr 1
  apply Test.interp_eq_of_eval
  intro v
  apply Bool.eq_iff_iff.mpr
  simpa only [testDisjunction_eval, Finset.mem_filter, Finset.mem_univ, true_and] using h i v

variable [BooleanAlphabet T]

private def guardTest (g : Guard T) : Test T :=
  g.1.toTest (BooleanAlphabet.numbering (T := T)).symm

private theorem guardTest_eval (g : Guard T) (v : Atom T) :
    (guardTest g).eval v = Boolean.eval g.1 (encodeAtom v) := Boolean.Diagram.toTest_correct _ _ _

private def regionTest {I : Type} [DecidableEq I] (regions : Regions T I) (i : I) : Test T :=
  labelTest (regions.map (fun (g, k) => (guardTest g, k))) i

private theorem regionTest_eval {I : Type} [DecidableEq I] (regions : Regions T I)
    (f : Atom T → I) (h : Covers regions f) (i : I) (v : Atom T) :
    (regionTest regions i).eval v = true ↔ i = f v := by
  simp only [regionTest, labelTest_eval, List.mem_map]
  constructor
  · rintro ⟨_, ⟨⟨g, k⟩, hk, he⟩, hv⟩
    cases he
    exact h.1 _ _ hk _ ((guardTest_eval (T := T) g v) ▸ hv)
  · rintro rfl
    obtain ⟨g, hg, hv⟩ := h.2 v
    exact ⟨_, ⟨(g, f v), hg, rfl⟩, (guardTest_eval (T := T) g v).trans hv⟩

variable [Encodable T] [Encodable A] [Fintype A] [DecidableEq T] [DecidableEq A]

omit [BooleanAlphabet T] [Encodable T] [Encodable A] [Fintype A] in
private theorem continuation_subset (p q : Expr T A) (h : q ∈ continuations p) :
    continuations q ⊆ continuations p := by
  induction p generalizing q with
  | zero | one | test => simp [continuations] at h
  | action a =>
    have eq : q = .one := Finset.mem_singleton.mp h
    subst q
    exact Finset.empty_subset _
  | plus p r hp hr =>
    exact (Finset.mem_union.mp h).elim (fun h => (hp _ h).trans Finset.subset_union_left)
      (fun h => (hr _ h).trans Finset.subset_union_right)
  | seq p r hp hr =>
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
      exact Finset.union_subset_union (Finset.image_subset_image (hp q hq)) (by rfl)
    · exact (hr _ h).trans Finset.subset_union_right
  | star p hp =>
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
    exact Finset.union_subset (Finset.image_subset_image (hp q hq)) (by rfl)

omit [BooleanAlphabet T] [Encodable T] [Encodable A] [Fintype A] in
private theorem continuation_supported {p q : Expr T A} (h : q ∈ support p) :
    continuations q ⊆ support p := by
  rcases Finset.mem_insert.mp h with rfl | h
  · exact Finset.subset_insert _ _
  · exact (continuation_subset _ _ h).trans (Finset.subset_insert _ _)

private abbrev Residual (p : Expr T A) := ↥(support p)

private def residualLabel {p : Expr T A} (q : Residual p) (a : A) (r : Residual p) : Test T :=
  labelTest (derivativeLabels q.val) (a, r.val)

private def extend {p : Expr T A} (x : Residual p → K) (r : Expr T A) : K :=
  if h : r ∈ support p then x ⟨r, h⟩ else 0

omit [BooleanAlphabet T] [Encodable T] [Encodable A] [Fintype A] in
private theorem extend_support {p : Expr T A} (x : Residual p → K) (r : Residual p) :
    extend x r.val = x r := dif_pos r.property

omit [BooleanAlphabet T] [Encodable T] [Encodable A] in
private theorem residual_affine (kat : KAT K B) (actions : A → K) (tests : T → B)
    (p : Expr T A) (q : Residual p) (x : Residual p → K) :
    affine (weighted kat actions tests residualLabel)
      (fun r : Residual p => kat.embed ((nullable r.val).interp tests)) x q =
      derivativeEquation kat actions tests (extend x) 1 q.val := by
  have h := labelTest_sum kat tests (derivativeLabels q.val) (Finset.univ ×ˢ support p)
    (fun (a, r) => actions a * extend x r)
    (fun l hl => Finset.mem_product.mpr ⟨Finset.mem_univ _,
      continuation_supported q.property (derivativeLabels_support _ _ hl)⟩)
  have h' := (derivativeLabels_weight kat actions tests (extend x) q.val).symm.trans h
  rw [Finset.sum_product] at h'
  simp only [affine, derivativeEquation, emptyWeight, mul_one]
  rw [h']
  simp only [weighted]
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_attach (support p)]
  simp only [Finset.univ_eq_attach, residualLabel, extend_support]

omit [BooleanAlphabet T] [Encodable T] [Encodable A] in
private theorem residual_solve (kat : KAT K B) (actions : A → K) (tests : T → B)
    (p : Expr T A) :
    solve (weighted kat actions tests residualLabel)
      (fun r : Residual p => kat.embed ((nullable r.val).interp tests)) =
      fun r => r.val.interp kat actions tests := by
  let y : Residual p → K := fun r => r.val.interp kat actions tests
  have eq (q : Residual p) :
      derivativeEquation kat actions tests (extend y) 1 q.val = y q := by
    simp only [derivativeEquation, mul_one]
    rw [← derivativeLabels_weight]
    have eqWeight :
        ((derivativeLabels q.val).map (fun (g, a, r) =>
          kat.embed (g.interp tests) * (actions a * extend y r))).sum =
        ((derivativeLabels q.val).map (fun (g, a, r) =>
          kat.embed (g.interp tests) * (actions a * (r.interp kat actions tests * 1)))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨g, a, r⟩ h
      have hr := continuation_supported q.property (derivativeLabels_support _ _ h)
      simp only [extend, dif_pos hr, y, mul_one]
    rw [eqWeight, derivativeLabels_weight kat actions tests
      (fun r => r.interp kat actions tests * 1)]
    simpa only [derivativeEquation, mul_one] using
      derivativeEquation_interp kat actions tests 1 q.val
  have hFixed : UpperSolution (weighted kat actions tests residualLabel)
      (fun r : Residual p => kat.embed ((nullable r.val).interp tests)) y := fun q =>
    (residual_affine kat actions tests p q y |>.trans (eq q)).le
  have hLeast (x : Residual p → K) (hx : UpperSolution (weighted kat actions tests residualLabel)
      (fun r : Residual p => kat.embed ((nullable r.val).interp tests)) x) (q : Residual p) :
      y q ≤ x q := by
    have h (r) (hr : r ∈ continuations q.val) :
        derivativeEquation kat actions tests (extend x) 1 r ≤ extend x r := by
      let r' : Residual p := ⟨r, continuation_supported q.property hr⟩
      rw [← residual_affine kat actions tests p r' x]
      exact (hx r').trans_eq (extend_support x r').symm
    have bound := interp_le_derivativeEquation kat actions tests q.val (extend x) 1 h
    rw [mul_one, ← residual_affine kat actions tests p q x] at bound
    exact bound.trans (hx q)
  let spec := solve_spec (weighted kat actions tests residualLabel)
    (fun r : Residual p => kat.embed ((nullable r.val).interp tests))
  exact le_antisymm (spec.2 y hFixed) (hLeast _ (fun i => (spec.1 i).le))

private abbrev Pair (p q : Expr T A) := ↥(explored p q)

private def pairStep {p q : Expr T A} (i : Pair p q) (v : Atom T) (a : A) : Pair p q :=
  ⟨(transition i.val.1 v a, transition i.val.2 v a), successor_explored i.property v a⟩

private def pairLabel {p q : Expr T A} (i : Pair p q) (a : A) (j : Pair p q) : Test T :=
  regionTest (pairRegions i.val a) j.val

private theorem pairLabel_eval {p q : Expr T A} (i j : Pair p q) (v : Atom T) (a : A) :
    (pairLabel i a j).eval v = true ↔ j = pairStep i v a := by
  rw [pairLabel, regionTest_eval _ _ (pairRegions_correct i.val a)]
  change (j.val = (pairStep i v a).val) ↔ _
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

private theorem project_solve (kat : KAT K B) (actions : A → K) (tests : T → B)
    (p q expression : Expr T A) (side : Pair p q → State T A)
    (hSide : ∀ i, side i ⊆ support expression)
    (hStep : ∀ i v a, side (pairStep i v a) = transition (side i) v a) :
    solve (weighted kat actions tests pairLabel)
      (fun i => kat.embed ((guardTest (outputGuard (side i))).interp tests)) =
      fun i => ∑ j : Residual expression,
        incidence (K := K) (fun i j => j.val ∈ side i) i j * j.val.interp kat actions tests := by
  have h₁ := weighted_intertwines kat actions tests pairLabel residualLabel
    (fun i (j : Residual expression) => j.val ∈ side i) (by
      intro i a j v
      simp only [pairLabel_eval, residualLabel, derivativeLabels_correct]
      constructor
      · rintro ⟨k, hk, rfl⟩
        rw [hStep, transition, Finset.mem_biUnion] at hk
        obtain ⟨r, hr, h⟩ := hk
        exact ⟨⟨r, hSide i hr⟩, hr, h⟩
      · rintro ⟨r, hr, h⟩
        refine ⟨pairStep i v a, ?_, rfl⟩
        rw [hStep, transition, Finset.mem_biUnion]
        exact ⟨r.val, hr, h⟩)
  have h₂ := output_intertwines kat tests
    (fun i => guardTest (outputGuard (side i))) (fun j : Residual expression => nullable j.val)
    (fun i j => j.val ∈ side i) (by
      intro i v
      simp only [guardTest_eval, outputGuard_correct, output, decide_eq_true_eq]
      constructor
      · rintro ⟨r, hr, h⟩
        exact ⟨⟨r, hSide i hr⟩, hr, h⟩
      · rintro ⟨r, hr, h⟩
        exact ⟨r.val, hr, h⟩)
  rw [show (fun i => kat.embed ((guardTest (outputGuard (side i))).interp tests)) =
    _ by exact funext h₂]
  rw [solve_intertwines _ _ _ _ h₁, residual_solve]

/-- The reachable symbolic pair system has the same least solution under
either projection when the solver checks that all its outputs agree. -/
theorem decideLanguageEquiv_algebraic (p q : Expr T A)
    (checked : decideLanguageEquiv p q = true)
    (kat : KAT K B) (actions : A → K) (tests : T → B) :
    p.interp kat actions tests = q.interp kat actions tests := by
  let first : Pair p q → State T A := fun i => i.val.1
  let second : Pair p q → State T A := fun i => i.val.2
  have hs₁ := project_solve kat actions tests p q p first
    (fun i => (explored_supported p q i.property).1) (fun _ _ _ => rfl)
  have hs₂ := project_solve kat actions tests p q q second
    (fun i => (explored_supported p q i.property).2) (fun _ _ _ => rfl)
  have outputs := of_decide_eq_true checked
  have hb : (fun i => kat.embed ((guardTest (outputGuard (first i))).interp tests)) =
      (fun i => kat.embed ((guardTest (outputGuard (second i))).interp tests)) := by
    funext i
    have eq : outputGuard (first i) = outputGuard (second i) :=
      of_decide_eq_true (outputs i.val i.property)
    rw [eq]
  rw [hb] at hs₁
  let start : Pair p q := ⟨initial p q, subset_saturate expand
    (fun s => Finset.subset_union_left) _ _ (Finset.mem_singleton_self _)⟩
  have eq := congrFun (hs₁.symm.trans hs₂) start
  have single (e : Expr T A) :
      (∑ j : Residual e, incidence (K := K) (fun (_ : Unit) j => j.val ∈ ({e} : State T A))
        () j * j.val.interp kat actions tests) = e.interp kat actions tests := by
    classical
    let r : Residual e := ⟨e, Finset.mem_insert_self _ _⟩
    rw [Finset.sum_eq_single r]
    · simp [incidence, r]
    · intro j _ h
      have hn : j.val ≠ e := fun eq => h (Subtype.ext eq)
      simp [incidence, hn]
    · simp
  exact (single p).symm.trans (eq.trans (single q))

end KATLean.Native
