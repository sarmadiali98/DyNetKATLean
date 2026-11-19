import KATLean.Native.Boolean

/-! Substitution and existential projection on the native ordered Boolean
trees. Both operations recurse on diagrams. -/

namespace KATLean.NetKAT.Guard

open Native.Boolean

def test (b : Bool) : Guard n := if b then truth else falsity

@[simp] theorem eval_test (b : Bool) (v : Fin n → Bool) : eval (test b).1 v = b := by
  cases b <;> rfl

def rename {n m : Nat} : Diagram n → (Fin n → Fin m) → Guard m
  | .leaf b, _ => test b
  | .skip d, f => rename d (fun i => f i.succ)
  | .node l r, f =>
    let g := atom m (f 0)
    disj (conj (neg g) (rename l (fun i => f i.succ)))
      (conj g (rename r (fun i => f i.succ)))

@[simp] theorem eval_rename (d : Diagram n) (f : Fin n → Fin m) (v : Fin m → Bool) :
    eval (rename d f).1 v = eval d (v ∘ f) := by
  induction d with
  | leaf b => simp [rename, eval]
  | skip d ih => exact ih _
  | node l r ihl ihr =>
    simp only [rename, eval_disj, eval_conj, eval_neg, atom_correct, eval, ihl, ihr, Function.comp_apply]
    cases v (f 0) <;> simp [Function.comp_def]

def project {n : Nat} : Diagram n → (Fin n → Bool) → Guard n
  | .leaf b, _ => test b
  | .skip d, erase =>
    let c := project d (fun i => erase i.succ)
    ⟨lift c.1, reduced_lift c.1 c.2⟩
  | .node l r, erase =>
    let low := project l (fun i => erase i.succ)
    let high := project r (fun i => erase i.succ)
    if erase 0 then
      let c := disj low high
      ⟨lift c.1, reduced_lift c.1 c.2⟩
    else ⟨mk low.1 high.1, reduced_mk _ _ low.2 high.2⟩

/-- Existentially choosing values for erased variables, with all other bits
fixed by the caller. The witness valuation is used only in the proof. -/
theorem eval_project (d : Diagram n) (erase v : Fin n → Bool) :
    eval (project d erase).1 v = true ↔
      ∃ w, (∀ i, erase i = false → w i = v i) ∧ eval d w = true := by
  induction d with
  | leaf b =>
    simp only [project, eval_test, eval]
    exact ⟨fun h => ⟨v, fun _ _ => rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  | skip d ih =>
    simp only [project, eval_lift, ih, eval]
    constructor
    · rintro ⟨w, h, hw⟩
      refine ⟨Fin.cases (v 0) w, ?_, ?_⟩
      · intro i
        refine Fin.cases (fun _ => by simp) (fun j hj => ?_) i
        simpa only [Fin.cases_succ] using h j hj
      · simpa only [Fin.cases_succ] using hw
    · rintro ⟨w, h, hw⟩
      exact ⟨fun i => w i.succ, fun i => h i.succ, hw⟩
  | @node k l r ihl ihr =>
    constructor
    · intro h
      have witness (b : Bool) (w : Fin _ → Bool)
          (hw : ∀ i, erase i.succ = false → w i = v i.succ)
          (hb : erase 0 = false → b = v 0)
          (hbranch : (if b then eval r w else eval l w) = true) :
          ∃ w, (∀ i, erase i = false → w i = v i) ∧ eval (.node l r) w = true := by
        refine ⟨Fin.cases b w, ?_, ?_⟩
        · intro i
          refine Fin.cases hb (fun j => hw j) i
        · simpa only [eval, Fin.cases_zero, Fin.cases_succ] using hbranch
      cases he : erase 0
      · cases hv : v 0
        · simp only [project, he, Bool.false_eq_true, ↓reduceIte, eval_mk, hv, ihl] at h
          obtain ⟨w, hw, hr⟩ := h
          exact witness false w hw (fun _ => hv.symm) hr
        · simp only [project, he, Bool.false_eq_true, ↓reduceIte, eval_mk, hv, ihr] at h
          obtain ⟨w, hw, hr⟩ := h
          exact witness true w hw (fun _ => hv.symm) hr
      · simp only [project, he, ↓reduceIte, eval_lift, eval_disj, Bool.or_eq_true, ihl, ihr] at h
        rcases h with ⟨w, hw, hr⟩ | ⟨w, hw, hr⟩
        · exact witness false w hw (fun h => by simp [he] at h) hr
        · exact witness true w hw (fun h => by simp [he] at h) hr
    · rintro ⟨w, hw, h⟩
      have ht : ∀ i : Fin k, erase i.succ = false → w i.succ = v i.succ := fun i => hw i.succ
      cases he : erase 0
      · have hs := hw 0 he
        cases hv : v 0
        · have hf : w 0 = false := hs.trans hv
          simp only [eval, hf, Bool.false_eq_true, ↓reduceIte] at h
          simp only [project, he, Bool.false_eq_true, ↓reduceIte, eval_mk, hv, ihl]
          exact ⟨fun i => w i.succ, ht, h⟩
        · have hf : w 0 = true := hs.trans hv
          simp only [eval, hf, ↓reduceIte] at h
          simp only [project, he, Bool.false_eq_true, ↓reduceIte, eval_mk, hv, ihr]
          exact ⟨fun i => w i.succ, ht, h⟩
      · simp only [project, he, ↓reduceIte, eval_lift, eval_disj, Bool.or_eq_true, ihl, ihr]
        cases hv : w 0
        · exact Or.inl ⟨fun i => w i.succ, ht, by simpa [eval, hv] using h⟩
        · exact Or.inr ⟨fun i => w i.succ, ht, by simpa [eval, hv] using h⟩

end KATLean.NetKAT.Guard
