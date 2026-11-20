import KATLean
import DyNetKAT.NetKAT.Semantics

/-! Interpretation of the existing dup-free AST in the KATLean packet model.
This bridge imports no DyNetKAT process modules or external backend. -/
namespace DyNetKAT.NetKAT

open scoped Computability

/-- The current packet API is an instance of the generic field interface. -/
abbrev ctxPacketModel := ctxSchema.model

theorem ctx_lookup (f : FieldName) (p : CtxPkt) :
    ctxPacketModel.lookup f p = Packet.get p f := rfl

theorem ctx_update (f : FieldName) (v : FieldValueEnum) (p : CtxPkt) :
    ctxPacketModel.update f v p = Packet.update p f v := rfl

/-- Boolean predicates interpret into the Boolean algebra of packet sets. -/
def predicateInterp {schema : PacketSchema} : Predicate schema → Set schema.Packet
  | .pFalse => ⊥
  | .pTrue => ⊤
  | .pFieldEq fe => {p | schema.model.lookup fe.field p = fe.value}
  | .pAnd p q => predicateInterp p ⊓ predicateInterp q
  | .pOr p q => predicateInterp p ⊔ predicateInterp q
  | .pNot p => (predicateInterp p)ᶜ

theorem predicateInterp_correct {schema : PacketSchema} (p : Predicate schema)
    (packet : schema.Packet) :
    packet ∈ predicateInterp p ↔ p.holds packet := by
  induction p <;> simp_all [predicateInterp, Predicate.holds, Predicate.eval,
    schema.lookup_eq]

/-- Compositional KA interpretation, with Boolean tests embedded by the KAT. -/
def katInterp {schema : PacketSchema} : NetKAT schema → KATLean.Rel schema.Packet
  | .drop => 0
  | .id => 1
  | .test p => KATLean.Rel.tests.embed (predicateInterp p)
  | .completeTest alpha => KATLean.Rel.test {p | holdsComplete alpha p}
  | .assign1 f v => schema.model.assign f v
  | .union p q => katInterp p + katInterp q
  | .seq p q => katInterp p * katInterp q
  | .star p => (katInterp p)∗

theorem katInterp_test (p : Predicate) :
    katInterp (.test p) = KATLean.Rel.tests.embed (predicateInterp p) := rfl

theorem katInterp_assign (f : FieldName) (v : FieldValueEnum) :
    (katInterp (schema := ctxSchema) (.assign1 f v)).holds p q ↔ q = Packet.update p f v := Iff.rfl

theorem katInterp_fieldTest (f : FieldName) (v : FieldValueEnum) :
    katInterp (NetKAT.fieldTest f v) = ctxPacketModel.filter f v := rfl

theorem katInterp_union (p q : NetKAT) :
    katInterp (.union p q) = katInterp p + katInterp q := rfl

theorem katInterp_seq (p q : NetKAT) :
    katInterp (.seq p q) = katInterp p * katInterp q := rfl

theorem katInterp_star (p : NetKAT) : katInterp (.star p) = (katInterp p)∗ := rfl

private theorem starClosure_iff_reflTransGen {P : Type} {r : P → P → Prop} {x y : P} :
    StarClosure r x y ↔ Relation.ReflTransGen r x y := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl
    | step first _ ih => exact ih.head first
  · intro path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl _
    | head first _ ih => exact .step first ih

/-- All AST constructors, including arbitrary star, agree with the existing
packet semantics. -/
theorem katInterp_correct {schema : PacketSchema} (policy : NetKAT schema) (p q : schema.Packet) :
    (katInterp policy).holds p q ↔ Semantics policy p q := by
  induction policy generalizing p q with
  | drop | id | completeTest | assign1 => rfl
  | test pred => exact and_congr (predicateInterp_correct pred p) Iff.rfl
  | union left right ihl ihr =>
    exact or_congr (ihl p q) (ihr p q)
  | seq left right ihl ihr =>
    change (∃ r, (katInterp left).holds p r ∧ (katInterp right).holds r q) ↔ _
    simp only [ihl, ihr, Semantics]
  | star policy ih =>
    change Relation.ReflTransGen (katInterp policy).holds p q ↔ StarClosure (Semantics policy) p q
    rw [starClosure_iff_reflTransGen]
    have relations : (katInterp policy).holds = Semantics policy := by
      funext x y
      exact propext (ih x y)
    rw [relations]

/-- Equality in the KATLean interpretation is the existing packet
semantic equivalence. This bridge is independent of derivability. -/
theorem katInterp_eq_iff {p q : NetKAT} :
    katInterp p = katInterp q ↔ ∀ x y, Semantics p x y ↔ Semantics q x y := by
  constructor
  · intro eq x y
    rw [← katInterp_correct p x y, ← katInterp_correct q x y, eq]
  · intro equivalent
    apply KATLean.Rel.ext_holds
    intro x y
    exact (katInterp_correct p x y).trans
      ((equivalent x y).trans (katInterp_correct q x y).symm)

end DyNetKAT.NetKAT
