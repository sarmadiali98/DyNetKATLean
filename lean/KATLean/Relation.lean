import KATLean.KAT
import Mathlib.Logic.Relation

namespace KATLean

/-- Packet relations, with left-to-right execution order for multiplication. -/
@[ext] structure Rel (P : Type*) where
  holds : P → P → Prop

namespace Rel

variable {P : Type*}

instance : Zero (Rel P) := ⟨⟨fun _ _ => False⟩⟩
instance : One (Rel P) := ⟨⟨Eq⟩⟩
instance : Add (Rel P) := ⟨fun r s => ⟨fun x y => r.holds x y ∨ s.holds x y⟩⟩
instance : Mul (Rel P) :=
  ⟨fun r s => ⟨fun x y => ∃ z, r.holds x z ∧ s.holds z y⟩⟩

@[simp] theorem zero_holds (x y : P) : (0 : Rel P).holds x y ↔ False := Iff.rfl
@[simp] theorem one_holds (x y : P) : (1 : Rel P).holds x y ↔ x = y := Iff.rfl
@[simp] theorem add_holds (r s : Rel P) (x y : P) :
    (r + s).holds x y ↔ r.holds x y ∨ s.holds x y := Iff.rfl
@[simp] theorem mul_holds (r s : Rel P) (x y : P) :
    (r * s).holds x y ↔ ∃ z, r.holds x z ∧ s.holds z y := Iff.rfl

@[ext] theorem ext_holds {r s : Rel P} (h : ∀ x y, r.holds x y ↔ s.holds x y) : r = s := by
  cases r
  cases s
  congr
  funext x y
  exact propext (h x y)

instance : Semiring (Rel P) where
  add_assoc := by
    intros
    apply ext_holds
    intros
    exact or_assoc
  zero_add := by
    intro r
    apply ext_holds
    intro x y
    simp
  add_zero := by
    intro r
    apply ext_holds
    intro x y
    simp
  add_comm := by
    intros
    apply ext_holds
    intros
    exact or_comm
  mul_assoc := by
    intro r s t
    apply ext_holds
    intro x y
    constructor
    · rintro ⟨z, ⟨w, hr, hs⟩, ht⟩
      exact ⟨w, hr, z, hs, ht⟩
    · rintro ⟨w, hr, z, hs, ht⟩
      exact ⟨z, ⟨w, hr, hs⟩, ht⟩
  one_mul := by
    intro r
    apply ext_holds
    intro x y
    constructor
    · rintro ⟨_, rfl, h⟩
      exact h
    · exact fun h => ⟨x, rfl, h⟩
  mul_one := by
    intro r
    apply ext_holds
    intro x y
    constructor
    · rintro ⟨_, h, rfl⟩
      exact h
    · exact fun h => ⟨y, h, rfl⟩
  left_distrib := by
    intro r s t
    apply ext_holds
    intro x y
    constructor
    · rintro ⟨z, hr, hs | ht⟩
      exacts [Or.inl ⟨z, hr, hs⟩, Or.inr ⟨z, hr, ht⟩]
    · rintro (⟨z, hr, hs⟩ | ⟨z, hr, ht⟩)
      exacts [⟨z, hr, Or.inl hs⟩, ⟨z, hr, Or.inr ht⟩]
  right_distrib := by
    intro r s t
    apply ext_holds
    intro x y
    constructor
    · rintro ⟨z, hr | hs, ht⟩
      exacts [Or.inl ⟨z, hr, ht⟩, Or.inr ⟨z, hs, ht⟩]
    · rintro (⟨z, hr, ht⟩ | ⟨z, hs, ht⟩)
      exacts [⟨z, Or.inl hr, ht⟩, ⟨z, Or.inr hs, ht⟩]
  zero_mul := by
    intro r
    apply ext_holds
    intro x y
    constructor
    · rintro ⟨_, impossible, _⟩
      exact impossible
    · exact False.elim
  mul_zero := by
    intro r
    apply ext_holds
    intro x y
    constructor
    · rintro ⟨_, _, impossible⟩
      exact impossible
    · exact False.elim
  nsmul := nsmulRec
  natCast n := if n = 0 then 0 else 1
  natCast_zero := by simp
  natCast_succ := by
    intro n
    cases n <;> apply ext_holds <;> intro x y <;>
      simp [Nat.succ_ne_zero]

instance : IdemSemiring (Rel P) :=
  IdemSemiring.ofSemiring (fun r => ext_holds (by intros; simp))

theorem le_iff {r s : Rel P} : r ≤ s ↔ ∀ x y, r.holds x y → s.holds x y := by
  rw [order_iff_add]
  constructor
  · intro eq x y h
    have : (r + s).holds x y := Or.inl h
    rwa [eq] at this
  · intro h
    apply ext_holds
    intro x y
    exact ⟨fun hr => hr.elim (h x y) id, Or.inr⟩

instance : KleeneAlgebra (Rel P) where
  kstar r := ⟨Relation.ReflTransGen r.holds⟩
  one_le_kstar := by
    intro r
    apply le_iff.mpr
    rintro x y rfl
    exact .refl
  mul_kstar_le_kstar := by
    intro r
    apply le_iff.mpr
    rintro x y ⟨z, first, rest⟩
    exact rest.head first
  kstar_mul_le_kstar := by
    intro r
    apply le_iff.mpr
    rintro x y ⟨z, rest, last⟩
    exact rest.tail last
  mul_kstar_le_self := by
    intro r s stable
    apply le_iff.mpr
    rintro x y ⟨z, first, rest⟩
    induction rest with
    | refl => exact first
    | tail _ last ih => exact le_iff.mp stable _ _ ⟨_, ih, last⟩
  kstar_mul_le_self := by
    intro r s stable
    apply le_iff.mpr
    rintro x y ⟨z, rest, last⟩
    induction rest using Relation.ReflTransGen.head_induction_on with
    | refl => exact last
    | head first _ ih => exact le_iff.mp stable _ _ ⟨_, first, ih⟩

def test (s : Set P) : Rel P := ⟨fun x y => x ∈ s ∧ x = y⟩
def action (update : P → P) : Rel P := ⟨fun x y => y = update x⟩

def tests : KAT (Rel P) (Set P) where
  embed := test
  injective := by
    intro s t eq
    ext x
    have h := congrArg (fun r : Rel P => r.holds x x) eq
    simpa [test] using h
  map_bot := ext_holds (by simp [test])
  map_top := ext_holds (by simp [test])
  map_sup := by
    intro s t
    apply ext_holds
    intro x y
    simp [test, or_and_right]
  map_inf := by
    intro s t
    apply ext_holds
    intro x y
    constructor
    · rintro ⟨⟨hs, ht⟩, rfl⟩
      exact ⟨x, ⟨hs, rfl⟩, ht, rfl⟩
    · rintro ⟨z, ⟨hs, rfl⟩, ht, rfl⟩
      exact ⟨⟨hs, ht⟩, rfl⟩

end Rel
end KATLean
