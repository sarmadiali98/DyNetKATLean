------------------------------------------------------------------------
-- Generalized packet model, parameterized over finite field types.
--
-- Per the paper (Def. 1, p. 5): "Let F = {f1,...,fn} be a set of field
-- names with values in Vi, for i in {1,...,n}. We call *network packet* a
-- function in F -> N."  The paper says "we consider network packets with
-- values in **finite** domains."
--
-- We parameterize over:
--   FieldType   : a finite type of field names
--   Value       : a single finite type of values (all fields share the same domain)
--
-- The concrete 4-field/4-value instance is preserved as a test fixture.
--
-- Design note: The paper uses per-field value domains Vi, but for the
-- formalization we use a single Value type since the paper's finiteness
-- argument applies equally. This avoids dependent-type complications in
-- Packet.update while preserving all semantic properties.
------------------------------------------------------------------------

import KATLean.NetKAT.Packet
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

namespace DyNetKAT.NetKAT

open Finset

------------------------------------------------------------------------
-- Parameterized packet type
------------------------------------------------------------------------

/-- A packet is a function from field names to values.
    Per Definition 1 (p. 5): sigma : F -> Values. -/
def Packet (FieldType : Type) (Value : Type) := FieldType -> Value

namespace Packet

/-- Get the value of a field from a packet. -/
def get {FieldType Value : Type} (p : Packet FieldType Value) (f : FieldType) : Value := p f

/-- Update a field's value in a packet. -/
def update {FieldType Value : Type} [DecidableEq FieldType]
    (p : Packet FieldType Value) (f : FieldType) (v : Value) :
    Packet FieldType Value :=
  fun f' => if f = f' then v else p f'

/-- Extensionality for packets. -/
@[ext]
theorem ext {FieldType Value : Type} (p q : Packet FieldType Value)
    (h : forall f, p f = q f) : p = q :=
  funext h

/-- Get after update (same field). -/
theorem get_update_same {FieldType Value : Type} [DecidableEq FieldType]
    (p : Packet FieldType Value) (f : FieldType) (v : Value) :
    get (update p f v) f = v := by
  simp [get, update, decide_eq_decide, dif_pos (rfl : f = f)]

/-- Get after update (different field). -/
theorem get_update_diff {FieldType Value : Type} [DecidableEq FieldType]
    (p : Packet FieldType Value) (f f' : FieldType) (v : Value)
    (h : f ≠ f') :
    get (update p f v) f' = get p f' := by
  simp [get, update, h]

/-- Update with same value is identity. -/
theorem update_id {FieldType Value : Type} [DecidableEq FieldType]
    (p : Packet FieldType Value) (f : FieldType) :
    update p f (p f) = p := by
  ext f'
  by_cases h : f = f'
  . subst h
    show (if f = f then p f else p f) = p f
    simp
  . show (if f = f' then p f else p f') = p f'
    simp [h]

/-- Overwriting same field twice: second wins. -/
theorem update_update_same {FieldType Value : Type} [DecidableEq FieldType]
    (p : Packet FieldType Value) (f : FieldType) (v1 v2 : Value) :
    update (update p f v1) f v2 = update p f v2 := by
  ext f'
  by_cases h : f = f'
  . subst h
    show (if f = f then v2 else (if f = f then v1 else p f)) = if f = f then v2 else p f
    simp
  . simp [update, h, if_neg]

/-- Overwriting distinct fields commutes. -/
theorem update_update_diff {FieldType Value : Type} [DecidableEq FieldType]
    (p : Packet FieldType Value) (f g : FieldType)
    (hfg : f ≠ g) (v : Value) (w : Value) :
    update (update p f v) g w = update (update p g w) f v := by
  ext h
  by_cases h1 : f = h
  . subst h1
    by_cases h2 : g = f
    . subst h2; contradiction
    . simp [update, if_pos (rfl : f = f), if_neg h2, if_neg hfg]
  . by_cases h2 : g = h
    . subst h2
      by_cases h3 : f = g
      . subst h3; contradiction
      . simp [update, if_pos (rfl : g = g), if_neg h3, if_neg (Ne.symm hfg), if_neg h1]
    . by_cases h3 : f = g
      . subst h3; contradiction
      . simp [update, if_neg h1, if_neg h2, if_neg h3]

end Packet

------------------------------------------------------------------------
-- Concrete field names and values (test fixture)
------------------------------------------------------------------------

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

/-- A field value: bounded finite domain for formalization. -/
inductive FieldValueEnum
  | v0    : FieldValueEnum
  | v1    : FieldValueEnum
  | v8    : FieldValueEnum
  | v9    : FieldValueEnum
  deriving Repr, DecidableEq

/-- Fintype instance for FieldValueEnum (4 values). -/
instance : Fintype FieldValueEnum where
  elems := {FieldValueEnum.v0, FieldValueEnum.v1, FieldValueEnum.v8, FieldValueEnum.v9}
  complete := by
    intro x
    cases x <;> simp

/-- Finite dependent field domains over total packet valuations. The model
supplies the KATLean lookup and update laws. -/
structure PacketSchema where
  Field : Type
  Value : Field → Type
  fieldEq : DecidableEq Field
  valueEq : ∀ f, DecidableEq (Value f)
  fieldFinite : Fintype Field
  valueFinite : ∀ f, Fintype (Value f)
  model : KATLean.NetKAT.PacketModel Field Value ((f : Field) → Value f)
  lookup_eq : ∀ f p, model.lookup f p = p f

def PacketSchema.Packet (s : PacketSchema) := (f : s.Field) → s.Value f

/-- Packet equality checks the fields of the two supplied packets. -/
def PacketSchema.packetEq (s : PacketSchema) : DecidableEq s.Packet :=
  letI := s.fieldFinite
  letI := s.valueEq
  inferInstanceAs (DecidableEq ((f : s.Field) → s.Value f))

/-- Point updates of dependent functions are the canonical packet model. -/
def PacketSchema.ofFields (F : Type) (V : F → Type)
    [DecidableEq F] [Fintype F] [∀ f, DecidableEq (V f)] [∀ f, Fintype (V f)] :
    PacketSchema where
  Field := F
  Value := V
  fieldEq := inferInstance
  valueEq := inferInstance
  fieldFinite := inferInstance
  valueFinite := inferInstance
  model :=
    { lookup := fun f p => p f
      update := fun f v p => Function.update p f v
      lookup_update := by intros; simp
      lookup_update_other := by intros; rw [Function.update_of_ne (Ne.symm ‹_ ≠ _›)]
      update_lookup := by intros; simp
      update_overwrite := by intros; simp
      update_commute := by intros; apply Function.update_comm; assumption }
  lookup_eq := by intros; rfl

/-- The compatibility schema retains the original executable packet update. -/
abbrev ctxSchema : PacketSchema where
  Field := FieldName
  Value := fun _ => FieldValueEnum
  fieldEq := inferInstance
  valueEq := fun _ => inferInstance
  fieldFinite := inferInstance
  valueFinite := fun _ => inferInstance
  model :=
    { lookup := fun f p => Packet.get p f
      update := fun f v p => Packet.update p f v
      lookup_update := fun f v p => Packet.get_update_same p f v
      lookup_update_other := fun f g v p h => Packet.get_update_diff p f g v h
      update_lookup := fun f p => Packet.update_id p f
      update_overwrite := fun f v w p => Packet.update_update_same p f v w
      update_commute := fun f g v w p h => Packet.update_update_diff p f g h v w }
  lookup_eq := by intros; rfl

/-- The concrete packet type. -/
abbrev CtxPkt := ctxSchema.Packet

/-- Fintype instance for `CtxPkt` (the concrete packet space).

`CtxPkt = FieldName → FieldValueEnum` is a function type whose domain and
codomain are both finite (`Fintype FieldName` and `Fintype FieldValueEnum`).
Mathlib's `Pi.instFintype` provides `Fintype (∀ i, β i)` for any finite
index type `ι` and family `β : ι → Type` with each `β i` finite.  We
instantiate it with the constant family `fun (_ : FieldName) => FieldValueEnum`,
which is definitionally `FieldName → FieldValueEnum = CtxPkt`. -/
instance : Fintype CtxPkt :=
  @Pi.instFintype FieldName (fun (_ : FieldName) => FieldValueEnum)
    (inferInstance : DecidableEq FieldName) (inferInstance : Fintype FieldName)
    (fun (_ : FieldName) => (inferInstance : Fintype FieldValueEnum))

set_option maxRecDepth 10000 in
theorem ctxPkt_card : Fintype.card CtxPkt = 256 := by decide

-- `CompleteTest` and `CompleteAssignmentValuation` are both `def`-aliases of
-- `CtxPkt` (a total function `FieldName → FieldValueEnum`).  Type-class inference
-- does not look through `def` transparency, so explicit `Fintype` instances are
-- registered after each `def` (see below) that transfer the `Fintype CtxPkt`
-- instance along the definitional equality.

----------------------------------------------------------------------
-- Field-value pairs (for Finset-based tests)
------------------------------------------------------------------------

/-- A field-value pair. -/
structure FieldEq (schema : PacketSchema := ctxSchema) where
  field : schema.Field
  value : schema.Value field

instance : Repr FieldEq where
  reprPrec fe _ :=
    "{ field := " ++ repr fe.field ++ ", value := " ++ repr fe.value ++ " }"

instance {schema : PacketSchema} : DecidableEq (FieldEq schema) := by
  letI := schema.fieldEq
  letI := schema.valueEq
  intro ⟨f, v⟩ ⟨g, w⟩
  by_cases fields : f = g
  · subst g
    exact decidable_of_iff (v = w) (by simp)
  · exact isFalse (fun equal => fields (congrArg FieldEq.field equal))

/-- Holds predicate for Finset-based tests (concrete, backward compat).
    A predicate alpha holds on packet p iff all listed field=value pairs match.
    Note: an empty Finset is the predicate "true" (not a complete test). -/
def holdsFinset (alpha : Finset FieldEq) (p : CtxPkt) : Prop :=
  forall (fe : FieldEq), fe ∈ alpha -> p fe.field = fe.value

------------------------------------------------------------------------
-- Complete tests and assignments (Definition 4, p. 8)
------------------------------------------------------------------------

/-- A complete test (alpha): a total valuation assigning a value to every field.
    Per Definition 4 (p. 8): f1=v1...fn=vn with vi in Vi for all i.
    Representation: a total function FieldName -> FieldValueEnum.
    A complete test assigns a value to EVERY field (no missing, no conflicts). -/
def CompleteTest := CtxPkt

/-- `CompleteTest` inherits finiteness from `CtxPkt` via the definitional
    equality `CompleteTest = CtxPkt`.  Type-class inference does not look
    through `def`, so we register an explicit instance. -/
instance : Fintype CompleteTest :=
  Eq.mpr (congrArg Fintype (show CompleteTest = CtxPkt from rfl))
    (inferInstance : Fintype CtxPkt)

/-- Holds predicate: a complete test alpha holds on packet sigma iff all
    field values match. Since alpha is total, this checks every field. -/
def holdsComplete {F : Type} {V : F → Type} (alpha sigma : (f : F) → V f) : Prop :=
  forall f, alpha f = sigma f

/-- **Complete-test uniqueness (Task 3D-1):** A complete test α holds on a
    packet σ if and only if σ is exactly α (as a total valuation).

    Since α and σ are both total functions `FieldName → FieldValueEnum`,
    `holdsComplete α σ` means `∀ f, α f = σ f`, which by function
    extensionality is exactly `α = σ`. This establishes that a complete
    test matches exactly one packet — its own representing valuation.

    This is the foundation for the normalization construction (Lemma 5):
    it guarantees that the complete-test component of a normal-form summand
    picks out a unique packet. -/
theorem holdsComplete_iff_eq {F : Type} {V : F → Type} (α σ : (f : F) → V f) :
    holdsComplete α σ ↔ σ = α := by
  -- holdsComplete α σ := ∀ f, α f = σ f  (by definition)
  -- By function extensionality: (∀ f, σ f = α f) ↔ σ = α.
  -- Since equality is symmetric (α f = σ f ↔ σ f = α f), we adjust.
  unfold holdsComplete
  -- Goal: (∀ f, α f = σ f) ↔ (σ = α)
  rw [funext_iff]
  -- Goal: (∀ f, α f = σ f) ↔ (∀ f, σ f = α f)
  apply forall_congr'
  intro f
  exact eq_comm

------------------------------------------------------------------------
-- Complete-assignment valuation representation (Definition 4, p. 8)
--
-- A complete assignment π = f₁←v₁ ··· fₙ←vₙ fixes exactly one value for
-- every field.  This is the direct dual of CompleteTest: a total function
-- FieldName → FieldValueEnum that determines the output packet independently
-- of the input.
--
-- The obsolete `CompleteAssignment := CtxPkt → CtxPkt` and `applyAssign`
-- definition have been removed (Task 2R-K).  This representation is now
-- the sole model of complete assignments, as defined by the paper
-- (Definition 4, p. 8).
------------------------------------------------------------------------

/-- A complete-assignment valuation (Definition 4, p. 8):
    a total function FieldName → FieldValueEnum that fixes exactly one
    value for every field, i.e. the dual of `CompleteTest`.

    Per Definition 4 (p. 8), a complete assignment π = f₁←v₁ · · · fₙ←vₙ
    overwrites *every* field of the input packet: the result σπ equals π
    itself.  This representation (a total valuation) is the direct dual of
    `CompleteTest`, also modeled as `CtxPkt`. -/
def CompleteAssignmentValuation := CtxPkt

/-- `CompleteAssignmentValuation` inherits finiteness from `CtxPkt` via the
    definitional equality `CompleteAssignmentValuation = CtxPkt`.  Type-class
    inference does not look through `def`, so we register an explicit instance. -/
instance : Fintype CompleteAssignmentValuation :=
  Eq.mpr (congrArg Fintype (show CompleteAssignmentValuation = CtxPkt from rfl))
    (inferInstance : Fintype CtxPkt)

/-- Apply a complete-assignment valuation to an input packet.

    Per Definition 4 (p. 8), a complete assignment π = f₁←v₁ ··· fₙ←vₙ
    overwrites *every* field of the input packet: the result σπ equals π
    itself — it is a total valuation that ignores the original packet.
    Hence the output depends only on π, not on σ. -/
def applyValuation (pi : CompleteAssignmentValuation) (_sigma : CtxPkt) : CtxPkt :=
  pi

/-- **Basic property of `applyValuation`:** for every valuation π, input
    packet σ, and field f, the result of applying π has field value π f.

    This states that applying a complete-assignment valuation yields a
    packet whose field values are exactly those fixed by the valuation,
    independently of the input packet. -/
theorem applyValuation_field
    (pi : CompleteAssignmentValuation) (sigma : CtxPkt) (f : FieldName) :
    (applyValuation pi sigma) f = pi f := by
  unfold applyValuation
  rfl

------------------------------------------------------------------------
-- Concrete examples
------------------------------------------------------------------------

/-- Example packet with tpSrc = v8. -/
def examplePacket : CtxPkt :=
  fun
  | .tpSrc => FieldValueEnum.v8
  | _ => FieldValueEnum.v0

/-- Example packet with tpSrc = v9. -/
def examplePacket9 : CtxPkt :=
  fun
  | .tpSrc => FieldValueEnum.v9
  | _ => FieldValueEnum.v0

/-- Single-field test tpSrc = v8 (as Finset for backward compat). -/
def testTpSrc8 : Finset FieldEq :=
  { ⟨FieldName.tpSrc, FieldValueEnum.v8⟩ }

/-- The empty test holds on all packets (predicate `true`, not a complete test). -/
theorem empty_holds (p : CtxPkt) : holdsFinset ∅ p := by
  intro fe h
  exact (Finset.not_mem_empty _ h).elim

/-- A concrete complete test: tpSrc = v8 and all other fields = v0. -/
def completeTestTpSrc8 : CtxPkt :=
  fun
  | .tpSrc => FieldValueEnum.v8
  | _ => FieldValueEnum.v0

/-- The single-field test tpSrc = v8 holds on examplePacket (Finset form). -/
theorem testTpSrc8_holds : holdsFinset testTpSrc8 examplePacket := by
  intro fe hfe
  have fe_eq : fe = ⟨FieldName.tpSrc, FieldValueEnum.v8⟩ := by
    exact Finset.mem_singleton.mp hfe
  subst fe_eq
  rfl

/-- The single-field test tpSrc = v8 does NOT hold on examplePacket9. -/
theorem testTpSrc8_fails_on_9 : ¬ holdsFinset testTpSrc8 examplePacket9 := by
  intro h
  have h' := h ⟨FieldName.tpSrc, FieldValueEnum.v8⟩ (Finset.mem_singleton_self _)
  dsimp [holdsFinset, examplePacket9] at h'
  contradiction

/-- The complete test tpSrc=v8 and (others=v0) holds on examplePacket. -/
theorem completeTestTpSrc8_holds : holdsComplete completeTestTpSrc8 examplePacket := by
  unfold holdsComplete
  intro f
  cases f <;> rfl

/-- The complete test does NOT hold on examplePacket9 (tpSrc mismatch). -/
theorem completeTestTpSrc8_fails_on_9 : ¬ holdsComplete completeTestTpSrc8 examplePacket9 := by
  intro h
  specialize h .tpSrc
  -- h states: completeTestTpSrc8 .tpSrc = examplePacket9 .tpSrc, i.e. v8 = v9
  have : FieldValueEnum.v8 = FieldValueEnum.v9 := by exact h
  cases this

end DyNetKAT.NetKAT
