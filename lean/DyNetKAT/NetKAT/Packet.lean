import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic

namespace DyNetKAT.NetKAT

open Finset

------------------------------------------------------------------------
-- Field types and values
------------------------------------------------------------------------
-- Per the DyNetKAT paper (arXiv:2102.10035v4, p. 5, §I-A), a packet is a
-- function from a finite set of field names to a finite set of values.
-- The sets **A** (complete tests) and **Π** (complete assignments) are finite.

/-- A field name (finite enumeration). -/
inductive FieldName
  | tpSrc : FieldName   -- source transport port
  | tpDst : FieldName   -- destination transport port
  | swId  : FieldName   -- switch ID
  | port  : FieldName   -- switch port
  deriving Repr, DecidableEq

/-- Fintype instance for FieldName (4 values). -/
instance : Fintype FieldName where
  elems := {FieldName.tpSrc, FieldName.tpDst, FieldName.swId, FieldName.port}
  complete := by
    intro x
    cases x <;> simp

/-! A field value: bounded finite domain for formalization. -/
inductive FieldValue
  | v0    : FieldValue
  | v1    : FieldValue
  | v8    : FieldValue
  | v9    : FieldValue
  deriving Repr, DecidableEq

/-- Fintype instance for FieldValue (4 values). -/
instance : Fintype FieldValue where
  elems := {FieldValue.v0, FieldValue.v1, FieldValue.v8, FieldValue.v9}
  complete := by
    intro x
    cases x <;> simp

------------------------------------------------------------------------
-- Packet model
------------------------------------------------------------------------

/-- A packet is a function from field names to field values. -/
def Packet := FieldName → FieldValue

------------------------------------------------------------------------
-- Packet operations
------------------------------------------------------------------------

namespace Packet

/-- Get field value from a packet. -/
def get (p : Packet) (f : FieldName) : FieldValue := p f

/-- Update field value in a packet. -/
def update (p : Packet) (f : FieldName) (v : FieldValue) : Packet :=
  fun f' => if f = f' then v else p f'

/-- Extensionality for packets. -/
theorem ext (p q : Packet) : (∀ f, p f = q f) → p = q := by
  intro h
  funext f
  exact h f

/-- Get after update (same field). -/
theorem get_update_same (p : Packet) (f : FieldName) (v : FieldValue) :
    get (update p f v) f = v := by
  simp [get, update]

/-- Get after update (different field). -/
theorem get_update_diff (p : Packet) (f f' : FieldName) (v : FieldValue)
    (h : f ≠ f') :
    get (update p f v) f' = get p f' := by
  simp [get, update, h]

end Packet

------------------------------------------------------------------------
-- Complete tests (set A)  [paper p. 5]
------------------------------------------------------------------------

/-- A field-value pair. -/
structure FieldEq where
  field : FieldName
  value : FieldValue
  deriving Repr, DecidableEq

/-- Holds predicate: α holds on packet p iff all pairs match. -/
def holds (α : Finset FieldEq) (p : Packet) : Prop :=
  ∀ (fe : FieldEq), fe ∈ α → p fe.field = fe.value

/-- The empty test holds on all packets. -/
theorem empty_holds (p : Packet) : holds ∅ p := by
  intro fe h
  cases h

------------------------------------------------------------------------
-- Complete assignments (set Π)  [paper p. 5]
------------------------------------------------------------------------

/-- A complete assignment specifies target values for fields. -/
def CompleteAssignment := Packet

/-- Apply assignment π to packet σ. -/
def applyAssign (π : CompleteAssignment) (_σ : Packet) : Packet := π

------------------------------------------------------------------------
-- Concrete examples
------------------------------------------------------------------------

/-- Example packet with tpSrc = 8. -/
def examplePacket : Packet :=
  fun
  | .tpSrc => FieldValue.v8
  | _ => FieldValue.v0

/-- Example packet with tpSrc = 9. -/
def examplePacket9 : Packet :=
  fun
  | .tpSrc => FieldValue.v9
  | _ => FieldValue.v0

/-- Test: tpSrc = 8. -/
def testTpSrc8 : Finset FieldEq :=
  { ⟨.tpSrc, .v8⟩ }

/-- The test tpSrc = 8 holds on examplePacket. -/
theorem testTpSrc8_holds : holds testTpSrc8 examplePacket := by
  intro fe hfe
  have fe_eq : fe = ⟨FieldName.tpSrc, FieldValue.v8⟩ := by
    exact Finset.mem_singleton.mp hfe
  subst fe_eq
  rfl

/-- The test tpSrc = 8 does NOT hold on examplePacket9. -/
theorem testTpSrc8_fails_on_9 : ¬ holds testTpSrc8 examplePacket9 := by
  intro h
  have h' := h ⟨FieldName.tpSrc, FieldValue.v8⟩ (Finset.mem_singleton_self _)
  dsimp at h'
  have : examplePacket9 FieldName.tpSrc = FieldValue.v9 := rfl
  rw [this] at h'
  cases h'

end DyNetKAT.NetKAT
