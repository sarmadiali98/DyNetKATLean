import KATLean.Native
import Lean.Util.FoldConsts

open KATLean.Native

namespace NativeKATCompletenessTests

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev E := Expr (Fin 2) (Fin 2)
private def a : E := .action 0
private def b : E := .action 1
private def g : Test (Fin 2) := .atom 0
private def h : Test (Fin 2) := .atom 1

example : Equational (.plus a a) a :=
  (decideEquiv_iff_equational _ _).mp (by decide)

example : Equational (.seq a (.seq b a)) (.seq (.seq a b) a) :=
  (decideEquiv_iff_equational _ _).mp (by decide)

example : Equational (.seq a (.plus b a)) (.plus (.seq a b) (.seq a a)) :=
  (decideEquiv_iff_equational _ _).mp (by decide)

example : Equational (.plus .one (.seq a (.star a))) (.star a) :=
  (decideEquiv_iff_equational _ _).mp (by decide)

-- Star denesting requires more than syntactic equality or one unfold.
private def denestingLeft := Expr.star (.plus a b)
private def denestingRight := Expr.seq (.star a) (.star (.seq b (.star a)))

#guard (explored denestingLeft denestingRight).card > 1

example : Equational denestingLeft denestingRight :=
  (decideEquiv_iff_equational _ _).mp (by decide)

example : AlgebraicallyEquivalent denestingLeft denestingRight :=
  (decideEquiv_iff_algebraicallyEquivalent _ _).mp (by decide)

example : Equational (.star (.star a)) (.star a) :=
  (decideEquiv_iff_equational _ _).mp (by decide)

example : Equational (A := Fin 2) (.test (.disj g (.neg g))) .one :=
  (decideEquiv_iff_equational _ _).mp (by decide)

private def lhs : E := .seq (.test (.disj (.conj g h) (.conj (.neg g) h))) (.star a)
private def rhs : E := .seq (.test (.neg (.disj (.neg h) (.conj g (.neg g))))) (.star a)
private def different : E := .seq (.test (.disj h (.conj g (.neg h)))) (.star a)

example : Equational lhs rhs :=
  (decideEquiv_iff_equational _ _).mp (by decide)

example : ¬ Equational lhs different :=
  decideEquiv_false_not_equational (by decide)

example : ¬ AlgebraicallyEquivalent a b :=
  decideEquiv_false_not_algebraicallyEquivalent (by decide)

example : decideEquiv (.plus a a) a = true :=
  (decideEquiv_iff_equational _ _).mpr (.plusIdem a)

example : Equational (T := Fin 0) (A := Fin 0) (.star .zero) .one :=
  (decideEquiv_iff_equational _ _).mp (by decide)

open Lean in
private partial def nativeDependencies (env : Environment) (pending : List Name)
    (seen : Std.HashSet Name := {}) : Std.HashSet Name :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then nativeDependencies env rest seen
    else
      let body := (env.find? name).bind ConstantInfo.value?
      let next := (body.map Expr.getUsedConstants).getD #[] |>.toList.filter (fun dependency =>
        dependency.toString.startsWith "KATLean.Native." ||
        dependency.toString.startsWith "_private.KATLean.Native.")
      nativeDependencies env (next ++ rest) (seen.insert name)

open Lean in
run_cmd do
  let env ← getEnv
  for name in [`DyNetKAT.NetKAT.CtxPkt, `DyNetKAT.NetKAT.netkatEquiv,
      `DyNetKAT.NetKAT.decodeBackendCandidate, `KATLean.Native.Explicit.decideLanguageEquiv] do
    if env.contains name then
      throwError "forbidden dependency in the native completeness imports: {name}"
  let dependencies := nativeDependencies env [``language_to_equational]
  for name in [``decideLanguageEquiv_algebraic, ``AlgebraicallyEquivalent.equational,
      ``FiniteSystem.solve_intertwines, ``FiniteSystem.solve_spec,
      ``interp_le_derivativeEquation, ``derivativeLabels_correct, ``Test.interp_eq_of_eval,
      ``pairRegions_correct] do
    unless dependencies.contains name do
      throwError "guarded-string completeness bypasses {name}"

#print axioms language_to_equational
#print axioms relational_to_equational
#print axioms relationalEquivalent_iff_equational
#print axioms decideEquiv_iff_equational
#print axioms algebraicallyEquivalent_iff_equational
#print axioms decideEquiv_iff_algebraicallyEquivalent
#print axioms decideEquiv_false_not_equational
#print axioms decideEquiv_false_not_algebraicallyEquivalent

end NativeKATCompletenessTests
