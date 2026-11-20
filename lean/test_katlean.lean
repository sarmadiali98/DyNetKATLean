import DyNetKAT.NetKAT.KATLean

open scoped Computability
open KATLean

namespace KATLeanTests

section Algebra
variable {K B : Type*} [KleeneAlgebra K] [BooleanAlgebra B]

example (a : K) : a + a = a := add_idem a
example (a b : K) : a + b = b ↔ a ≤ b := (order_iff_add a b).symm
example (a b c : K) : a * (b + c) = a * b + a * c := mul_add a b c
example (a b c : K) : (a + b) * c = a * c + b * c := add_mul a b c
example (p : K) : 1 + p * p∗ = p∗ := star_unfold_left p
example (p : K) : 1 + p∗ * p = p∗ := star_unfold_right p
example (p q r : K) (h : q + p * r ≤ r) : p∗ * q ≤ r := star_induction_left h
example (p q r : K) (h : p + q * r ≤ q) : p * r∗ ≤ q := star_induction_right h
example (p q r : K) (h : (q + p * r) + r = r) : p∗ * q + r = r :=
  star_induction_left_add h
example (p q r : K) (h : (p + q * r) + q = q) : p * r∗ + q = q :=
  star_induction_right_add h
example (p q : K) (h : p ≤ q) : p∗ ≤ q∗ := kstar_mono h

example (kat : KAT K B) (a : B) : kat.embed a + kat.embed aᶜ = 1 := kat.excluded_middle a
example (kat : KAT K B) (a : B) : kat.embed a * kat.embed aᶜ = 0 := kat.contradiction a
example (kat : KAT K B) (a b : B) : kat.embed (a ⊔ b) = kat.embed a + kat.embed b := kat.map_sup a b
example (kat : KAT K B) (a b : B) : kat.embed (a ⊓ b) = kat.embed a * kat.embed b := kat.map_inf a b
example (kat : KAT K B) (a b : B) : kat.embed a ≤ kat.embed b ↔ a ≤ b := kat.order_iff a b
example (kat : KAT K B) (a : B) : kat.embed a + 1 = 1 := kat.plus_one a
example (kat : KAT K B) (a : B) : kat.embed a * kat.embed a = kat.embed a := kat.test_idempotent a
example (kat : KAT K B) (a b : B) : kat.embed a * kat.embed b = kat.embed b * kat.embed a :=
  kat.test_commute a b
example (kat : KAT K B) (a b c : B) :
    kat.embed a + kat.embed b * kat.embed c =
      (kat.embed a + kat.embed b) * (kat.embed a + kat.embed c) := kat.plus_distrib a b c
end Algebra

section Packets
variable {F : Type*} {V : F → Type*} {P : Type*}
variable (model : NetKAT.PacketModel F V P) (f g : F) (v : V f) (w : V g)

example : model.filter f v * model.filter g w = model.filter g w * model.filter f v :=
  model.filter_commute f g v w
example (h : f ≠ g) : model.assign f v * model.assign g w = model.assign g w * model.assign f v :=
  model.assign_commute f g v w h
example (h : f ≠ g) : model.assign f v * model.filter g w = model.filter g w * model.assign f v :=
  model.assign_filter_commute f g v w h
example (other : V f) : model.assign f v * model.assign f other = model.assign f other :=
  model.overwrite f v other
example : model.assign f v * model.filter f v = model.assign f v := model.assign_filter f v
example : model.filter f v * model.assign f v = model.filter f v := model.filter_assign f v
example : model.filter f v * model.filter f v = model.filter f v := model.filter_idempotent f v
example (other : V f) (h : v ≠ other) : model.filter f v * model.filter f other = 0 :=
  model.filter_contradiction f v other h
example [Fintype (V f)] : (∑ value : V f, model.filter f value) = 1 := model.match_all f
end Packets

open DyNetKAT.NetKAT

-- A complete policy equation proved by the KATLean packet law.
theorem policy_overwrite :
    katInterp (.seq ((.assign1 .port .v0 : NetKAT)) ((.assign1 .port .v1 : NetKAT))) =
      katInterp ((.assign1 .port .v1 : NetKAT)) :=
  ctxPacketModel.overwrite .port .v0 .v1

example : ctxPacketModel.lookup .port (ctxPacketModel.update .port .v8 p) = .v8 :=
  ctxPacketModel.lookup_update .port .v8 p

example : ctxPacketModel.assign .tpSrc .v8 * ctxPacketModel.assign .port .v1 =
    ctxPacketModel.assign .port .v1 * ctxPacketModel.assign .tpSrc .v8 :=
  ctxPacketModel.assign_commute _ _ _ _ (by decide)

example (p q : CtxPkt) :
    (katInterp (NetKAT.fieldTest .port .v8)).holds p q ↔ p .port = .v8 ∧ p = q := Iff.rfl

example (policy : DyNetKAT.NetKAT.NetKAT) (p q : CtxPkt) :
    (katInterp (.star (.star policy))).holds p q ↔ Semantics (.star (.star policy)) p q :=
  katInterp_correct _ _ _

example (p : CtxPkt) : ∃ outputs, execute (.star ((.assign1 .port .v1 : NetKAT))) p = .supported outputs ∧
    ∀ q, q ∈ outputs ↔ (katInterp (.star ((.assign1 .port .v1 : NetKAT)))).holds p q :=
  execute_katInterp _ p

example : katInterp (.seq ((.assign1 .port .v0 : NetKAT)) ((.assign1 .port .v1 : NetKAT))) =
    katInterp ((.assign1 .port .v1 : NetKAT)) :=
  (Derives.paModMod .port .v0 .v1).katSound

example (policy : DyNetKAT.NetKAT.NetKAT) : katInterp policy = katInterp (normalize policy) :=
  normalize_katInterp policy

#print axioms star_induction_left_add
#print axioms star_induction_right_add
#print axioms star_unfold_left
#print axioms KAT.contradiction
#print axioms KAT.order_iff
#print axioms Rel.tests
#print axioms NetKAT.PacketModel.assign_commute
#print axioms NetKAT.PacketModel.assign_filter_commute
#print axioms NetKAT.PacketModel.overwrite
#print axioms NetKAT.PacketModel.match_all
#print axioms ctxPacketModel
#print axioms katInterp_correct
#print axioms execute_katInterp
#print axioms Derives.katSound
#print axioms normalize_katInterp

end KATLeanTests
