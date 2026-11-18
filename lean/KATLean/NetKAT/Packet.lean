import KATLean.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace KATLean.NetKAT

/-- Only the lookup/update interface and laws needed by Figure 4.
Value domains may depend on the field. Finiteness is needed only for
PA-MATCH-ALL. -/
structure PacketModel (Field : Type*) (Value : Field → Type*) (Packet : Type*) where
  lookup : (f : Field) → Packet → Value f
  update : (f : Field) → Value f → Packet → Packet
  lookup_update : ∀ f v p, lookup f (update f v p) = v
  lookup_update_other : ∀ f g v p, f ≠ g → lookup g (update f v p) = lookup g p
  update_lookup : ∀ f p, update f (lookup f p) p = p
  update_overwrite : ∀ f v w p, update f w (update f v p) = update f w p
  update_commute : ∀ f g v w p, f ≠ g →
    update g w (update f v p) = update f v (update g w p)

namespace PacketModel

variable {F : Type*} {V : F → Type*} {P : Type*} (model : PacketModel F V P)

def filter (f : F) (v : V f) : Rel P := Rel.test {p | model.lookup f p = v}
def assign (f : F) (v : V f) : Rel P := Rel.action (model.update f v)

@[simp] theorem filter_holds (f : F) (v : V f) (p q : P) :
    (model.filter f v).holds p q ↔ model.lookup f p = v ∧ p = q := Iff.rfl

@[simp] theorem assign_holds (f : F) (v : V f) (p q : P) :
    (model.assign f v).holds p q ↔ q = model.update f v p := Iff.rfl

/-- Tests commute even on the same field (BA-SEQ-COMM). -/
theorem filter_commute (f g : F) (v : V f) (w : V g) :
    model.filter f v * model.filter g w = model.filter g w * model.filter f v :=
  Rel.tests.test_commute _ _

/-- PA-MOD-MOD-COMM. -/
theorem assign_commute (f g : F) (v : V f) (w : V g) (h : f ≠ g) :
    model.assign f v * model.assign g w = model.assign g w * model.assign f v := by
  apply Rel.ext_holds
  intro p q
  change (∃ r, r = _ ∧ q = _) ↔ (∃ r, r = _ ∧ q = _)
  simp only [exists_eq_left]
  rw [model.update_commute f g v w p h]

/-- PA-MOD-FILTER-COMM. -/
theorem assign_filter_commute (f g : F) (v : V f) (w : V g) (h : f ≠ g) :
    model.assign f v * model.filter g w = model.filter g w * model.assign f v := by
  apply Rel.ext_holds
  intro p q
  change (∃ r, r = _ ∧ model.lookup g r = w ∧ r = q) ↔
    (∃ r, (model.lookup g p = w ∧ p = r) ∧ q = model.update f v r)
  simp only [exists_eq_left, model.lookup_update_other f g v p h, exists_eq_right]
  constructor
  · rintro ⟨value, target⟩
    exact ⟨p, ⟨value, rfl⟩, target.symm⟩
  · rintro ⟨r, ⟨value, rfl⟩, target⟩
    exact ⟨value, target.symm⟩

/-- PA-MOD-MOD. -/
theorem overwrite (f : F) (v w : V f) :
    model.assign f v * model.assign f w = model.assign f w := by
  apply Rel.ext_holds
  intro p q
  change (∃ r, r = _ ∧ q = _) ↔ q = _
  simp only [exists_eq_left, model.update_overwrite]

/-- PA-MOD-FILTER. -/
theorem assign_filter (f : F) (v : V f) :
    model.assign f v * model.filter f v = model.assign f v := by
  apply Rel.ext_holds
  intro p q
  change (∃ r, r = _ ∧ model.lookup f r = v ∧ r = q) ↔ q = _
  simp only [exists_eq_left, model.lookup_update, true_and]
  exact eq_comm

/-- PA-FILTER-MOD. -/
theorem filter_assign (f : F) (v : V f) :
    model.filter f v * model.assign f v = model.filter f v := by
  apply Rel.ext_holds
  intro p q
  change (∃ r, (model.lookup f p = v ∧ p = r) ∧ q = model.update f v r) ↔
    model.lookup f p = v ∧ p = q
  constructor
  · rintro ⟨r, ⟨value, rfl⟩, rfl⟩
    exact ⟨value, (value ▸ model.update_lookup f p).symm⟩
  · rintro ⟨value, rfl⟩
    exact ⟨p, ⟨value, rfl⟩, value ▸ (model.update_lookup f p).symm⟩

theorem filter_idempotent (f : F) (v : V f) :
    model.filter f v * model.filter f v = model.filter f v :=
  Rel.tests.test_idempotent _

/-- PA-CONTRA. -/
theorem filter_contradiction (f : F) (v w : V f) (different : v ≠ w) :
    model.filter f v * model.filter f w = 0 := by
  apply Rel.ext_holds
  intro p q
  constructor
  · rintro ⟨r, ⟨first, rfl⟩, second, _⟩
    exact different (first.symm.trans second)
  · exact False.elim

private theorem sum_holds {I : Type*} (s : Finset I) (r : I → Rel P) (p q : P) :
    (∑ i ∈ s, r i).holds p q ↔ ∃ i ∈ s, (r i).holds p q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Zero.zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    change ((r i).holds p q ∨ _) ↔ _
    rw [ih]
    simp

/-- PA-MATCH-ALL, over the declared finite value domain of the field. -/
theorem match_all (f : F) [Fintype (V f)] :
    (∑ v : V f, model.filter f v) = 1 := by
  apply Rel.ext_holds
  intro p q
  rw [sum_holds]
  change (∃ v ∈ Finset.univ, model.lookup f p = v ∧ p = q) ↔ p = q
  simp

end PacketModel
end KATLean.NetKAT
