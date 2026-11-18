import KATLean.Native
import Lean.Util.FoldConsts

open KATLean.Native

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace NativeKATTests

abbrev E := Expr (Fin 1) (Fin 2)
private def a : E := .action 0
private def b : E := .action 1
private def guard : Test (Fin 1) := .atom 0

#guard !decideEquiv (T := Fin 1) (A := Fin 2) .zero .one
#guard decideEquiv (.plus a a) a
#guard decideEquiv (.plus a (.plus b .one)) (.plus (.plus a b) .one)
#guard decideEquiv (.seq a (.seq b a)) (.seq (.seq a b) a)
#guard decideEquiv (.seq a (.plus b a)) (.plus (.seq a b) (.seq a a))
#guard decideEquiv (.seq (.plus a b) a) (.plus (.seq a a) (.seq b a))
#guard decideEquiv (.plus .one (.seq a (.star a))) (.star a)
#guard decideEquiv (.plus .one (.seq (.star a) a)) (.star a)
#guard decideEquiv (.star (.star a)) (.star a)
#guard decideEquiv (.star (.plus .one a)) (.star a)
#guard decideEquiv (.star (.plus a b)) (.seq (.star a) (.star (.seq b (.star a))))
#guard !decideEquiv (.seq a b) (.seq b a)
#guard !decideEquiv a (.plus .one a)
#guard decideEquiv (T := Fin 1) (A := Fin 2) (.test (.disj guard (.neg guard))) .one
#guard decideEquiv (T := Fin 1) (A := Fin 2) (.test (.conj guard (.neg guard))) .zero
-- Tests at successive positions may differ. These must remain inequivalent.
#guard !decideEquiv (.seq (.test guard) a) (.seq a (.test guard))
-- A consequence of star induction mixing Boolean and action reasoning.
#guard decideEquiv (.seq (.test guard) (.star (.seq (.test (.neg guard)) a))) (.test guard)
#guard (explored (.seq a b) (.seq a a)).card > 1

-- Empty primitive alphabets and a larger independent test alphabet are supported.
#guard decideEquiv (T := Fin 0) (A := Fin 0) (.star .zero) .one
#guard decideEquiv (T := Fin 2) (A := Fin 0)
  (.test (.conj (.atom 0) (.disj (.atom 0) (.atom 1)))) (.test (.atom 0))

example : RelationalEquivalent (.plus a a) a := decideEquiv_sound _ _ (by decide)
example (P : Type) (actions : Fin 2 → KATLean.Rel P) (tests : Fin 1 → Set P) :
    Expr.interp KATLean.Rel.tests actions tests (.star (.star a)) =
      Expr.interp KATLean.Rel.tests actions tests (.star a) :=
  decideEquiv_sound _ _ (by decide) P actions tests

example : ∃ atom word, ¬ (Accept (.zero : E) atom word ↔ Accept (.one : E) atom word) :=
  inequivalent_witness _ _ (by decide)

#eval ((support (.star (.plus a b))).card,
  (support (.seq (.star a) (.star (.seq b (.star a))))).card,
  (explored (.star (.plus a b)) (.seq (.star a) (.star (.seq b (.star a))))).card)

-- The solver proof environment is independent of the concrete packet model.
open Lean in
run_cmd do
  let env ← getEnv
  for forbidden in [`DyNetKAT.NetKAT.CtxPkt, `DyNetKAT.NetKAT.netkatEquiv,
      `DyNetKAT.NetKAT.execute, `DyNetKAT.NetKAT.katchSemantics] do
    if env.contains forbidden then
      throwError "native proof imports concrete or external solver {forbidden}"

#print axioms nullable_correct
#print axioms derivative_correct
#print axioms continuations_closed
#print axioms state_space_finite
#print axioms saturate_closed
#print axioms decideLanguageEquiv_correct
#print axioms interp_iff_accept
#print axioms guarded_model_correct
#print axioms decideEquiv_sound
#print axioms decideEquiv_complete
#print axioms decideEquiv_correct
#print axioms inequivalent_witness

end NativeKATTests
