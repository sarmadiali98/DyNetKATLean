import DyNetKAT
import Lean.Util.FoldConsts

set_option linter.dupNamespace false

namespace DyNetKAT.NetKAT.KATLeanDerivesTests

local infixl:65 " ⊕ " => NetKAT.union
local infixl:70 " ⨟ " => NetKAT.seq

variable (p q r : NetKAT)

theorem assoc_algebra : katInterp (p ⨟ (q ⨟ r)) = katInterp ((p ⨟ q) ⨟ r) :=
  (Derives.seqAssoc p q r).katSound

example : katInterp (p ⊕ p) = katInterp p := (Derives.plusIdem p).katSound
example : katInterp (.id ⊕ (p ⨟ .star p)) = katInterp (.star p) := (Derives.unrollL p).katSound
example : katInterp (.id ⊕ (.star p ⨟ p)) = katInterp (.star p) := (Derives.unrollR p).katSound

example (hypothesis : Derives ((q ⊕ (p ⨟ r)) ⊕ r) r) :
    katInterp ((.star p ⨟ q) ⊕ r) = katInterp r :=
  (Derives.lfpL hypothesis).katSound

example (hypothesis : Derives ((p ⊕ (q ⨟ r)) ⊕ q) q) :
    katInterp ((p ⨟ .star r) ⊕ q) = katInterp q :=
  (Derives.lfpR hypothesis).katSound

example : Derives ((.star p ⨟ .id) ⊕ .star p) (.star p) :=
  .lfpL (.trans (.unionCongr (.unrollL p) (.refl _)) (.plusIdem _))

example : Derives ((.id ⨟ .star p) ⊕ .star p) (.star p) :=
  .lfpR (.trans (.unionCongr (.unrollR p) (.refl _)) (.plusIdem _))

theorem complement_algebra (test : Predicate) :
    katInterp (.test test ⊕ .test (.pNot test)) = katInterp .id :=
  (Derives.baExclMid test).katSound

example (test : Predicate) : katInterp (.test test ⨟ .test (.pNot test)) = katInterp .drop :=
  (Derives.baContra test).katSound

example (test other : Predicate) (equal : Derives (.test test) (.test other)) :
    katInterp (.test (.pNot test)) = katInterp (.test (.pNot other)) :=
  (Derives.notCongr equal).katSound

theorem packet_algebra :
    katInterp ((.assign1 .port .v0 : NetKAT) ⨟ (.assign1 .tpSrc .v8 : NetKAT)) =
      katInterp ((.assign1 .tpSrc .v8 : NetKAT) ⨟ (.assign1 .port .v0 : NetKAT)) :=
  (Derives.paModModComm (schema := ctxSchema) .port .tpSrc .v0 .v8 (by decide)).katSound

example : katInterp ((.assign1 .port .v0 : NetKAT) ⨟ (.assign1 .port .v1 : NetKAT)) = katInterp ((.assign1 .port .v1 : NetKAT)) :=
  (Derives.paModMod (schema := ctxSchema) .port .v0 .v1).katSound

example : katInterp ((.assign1 .port .v1 : NetKAT) ⨟ NetKAT.fieldTest .port .v1) =
    katInterp ((.assign1 .port .v1 : NetKAT)) := (Derives.paModFilter (schema := ctxSchema) .port .v1).katSound

example : katInterp (NetKAT.fieldTest .port .v1 ⨟ .assign1 .port .v1) =
    katInterp (NetKAT.fieldTest .port .v1) := (Derives.paFilterMod (schema := ctxSchema) .port .v1).katSound

example : katInterp (NetKAT.fieldTest .port .v0 ⨟ NetKAT.fieldTest .port .v1) = katInterp .drop :=
  (Derives.paContra (schema := ctxSchema) .port .v0 .v1 (by decide)).katSound

example : katInterp (matchAll .port) = katInterp .id := (Derives.paMatchAll .port).katSound

theorem normalization_soundness : ∀ x y, Semantics p x y ↔ Semantics (normalize p) x y :=
  (normalize_derives p).sound

-- This test checks proof-body constants, beyond the axiom audit. In
-- particular katSound must use the KA, KAT and packet laws directly.
open Lean in
run_cmd do
  let env ← getEnv
  let some algebraic := (env.find? ``Derives.katSound).bind ConstantInfo.value? |
    throwError "missing algebraic soundness proof"
  let used := algebraic.getUsedConstants
  for expected in #[``add_assoc, ``add_comm, ``add_zero, ``add_idem, ``mul_assoc,
      ``one_mul, ``mul_one, ``mul_add, ``add_mul, ``zero_mul, ``mul_zero,
      ``KATLean.star_unfold_left, ``KATLean.star_unfold_right,
      ``KATLean.star_induction_left_add, ``KATLean.star_induction_right_add,
      ``KATLean.KAT.map_bot, ``KATLean.KAT.map_top, ``KATLean.KAT.map_sup, ``KATLean.KAT.map_inf,
      ``KATLean.KAT.plus_distrib, ``KATLean.KAT.plus_one, ``KATLean.KAT.excluded_middle,
      ``KATLean.KAT.test_commute, ``KATLean.KAT.contradiction, ``KATLean.KAT.test_idempotent,
      ``KATLean.NetKAT.PacketModel.assign_commute, ``KATLean.NetKAT.PacketModel.assign_filter_commute,
      ``KATLean.NetKAT.PacketModel.assign_filter, ``KATLean.NetKAT.PacketModel.filter_assign,
      ``KATLean.NetKAT.PacketModel.overwrite, ``KATLean.NetKAT.PacketModel.filter_contradiction,
      ``KATLean.NetKAT.PacketModel.match_all] do
    unless used.contains expected do
      throwError "algebraic soundness does not reference {expected}"
  if used.contains ``Derives.sound then
    throwError "algebraic soundness depends on old semantic soundness"
  let some semantic := (env.find? ``Derives.sound).bind ConstantInfo.value? |
    throwError "missing semantic soundness proof"
  unless semantic.getUsedConstants.contains ``Derives.katSound do
    throwError "semantic soundness bypasses algebraic soundness"
  for (consumer, foundation) in #[(``Derives.historySound, ``Derives.sound),
      (``_root_.DyNetKAT.DyNetKAT.Equations.netkat_sound, ``Derives.historySound),
      (``normalize_katInterp, ``Derives.katSound)] do
    let some body := (env.find? consumer).bind ConstantInfo.value? |
      throwError "missing downstream proof {consumer}"
    unless body.getUsedConstants.contains foundation do
      throwError "{consumer} bypasses {foundation}"
  for name in [`DyNetKAT.NetKAT.katchSemantics, `DyNetKAT.NetKAT.decodeBackendCandidate] do
    if env.contains name then
      throwError "optional backend leaked into core imports"

open KATLean.Native in
example (actions : Fin 2 → NetKAT) (tests : Fin 1 → Predicate) :
    Derives
      (nativeEmbed actions tests (.star (.star (.action 0))))
      (nativeEmbed actions tests (.star (.action 0))) :=
  nativeSolver_derives (by decide) actions tests

open KATLean.Native in
example (tests : Fin 1 → Predicate) :
    Derives (nativeEmbed (fun _ : Fin 2 => NetKAT.id) tests (.action 0))
      (nativeEmbed (fun _ : Fin 2 => NetKAT.id) tests (.action 1)) ∧
    decideEquiv (T := Fin 1) (A := Fin 2) (.action 0) (.action 1) = false :=
  ⟨.refl _, by decide⟩

open KATLean.Native in
example (actions : Fin 2 → NetKAT) (tests : Fin 8 → Predicate) :
    let a : Expr (Fin 8) (Fin 2) := .action 0
    Derives (nativeEmbed actions tests (.plus a a)) (nativeEmbed actions tests a) :=
  nativeEquational_derives (.plusIdem (.action 0)) actions tests

#print axioms nativeSolver_derives
#print axioms nativeEquational_derives
#print axioms Derives.sound
#print axioms Derives.katSound
#print axioms assoc_algebra
#print axioms complement_algebra
#print axioms packet_algebra
#print axioms normalization_soundness
#print axioms _root_.DyNetKAT.DyNetKAT.Equations.netkat_sound

end DyNetKAT.NetKAT.KATLeanDerivesTests

namespace DyNetKAT.DyNetKAT.KATLeanPrefixTests

open DyNetKAT.NetKAT

theorem packet_prefix (env : RecEnv) (rest : DyNetKAT) :
    Bisimilar env (.nSeq (.union .id .drop) rest) (.nSeq .id rest) :=
  (DerivesNoAIP.netkat rest (NetKAT.Derives.plusZero .id)).sound

-- Identical packet meanings still give distinct observable send labels.
theorem literal_payload (env : RecEnv) (rest : DyNetKAT) :
    ¬ DerivesNoAIP env (.send "x" (.union .id .drop) rest) (.send "x" .id rest) := by
  intro proof
  obtain ⟨relation, bisimulation, related⟩ := proof.sound
  obtain ⟨_, step, _⟩ := bisimulation.2 _ _ related [] []
    (.send "x" (.union .id .drop)) rest [] [] (.cpol_send _ _ _ _ _)
  cases step

#print axioms packet_prefix
#print axioms literal_payload

end DyNetKAT.DyNetKAT.KATLeanPrefixTests
