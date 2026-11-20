import DyNetKAT.NetKAT.Symbolic
import Lean.Util.FoldConsts

namespace SymbolicNetKATTests

open DyNetKAT.NetKAT
open KATLean.Native
open KATLean.Native.Boolean

local infixl:65 " ∔ " => NetKAT.union
local infixl:70 " ⨟ " => NetKAT.seq

private def port (a : FieldValueEnum) := NetKAT.fieldTest .port a
private def write (a : FieldValueEnum) : NetKAT := NetKAT.assign1 .port a
private def sw (a : FieldValueEnum) : NetKAT := NetKAT.assign1 .swId a
private def protectedInput : Predicate :=
  .pAnd (.fieldEq .tpSrc .v8)
    (.pNot (.pOr (.fieldEq .port .v1) (.pAnd (.fieldEq .swId .v0) (.fieldEq .swId .v9))))

private def firewall : NetKAT := .test protectedInput ⨟ write .v1 ⨟ sw .v9
private def step : NetKAT :=
  (port .v0 ⨟ write .v1 ⨟ sw .v8) ∔
  (port .v1 ⨟ write .v8 ⨟ sw .v9) ∔
  (port .v8 ⨟ write .v9)
private def route : NetKAT := port .v0 ⨟ .star (.star step) ⨟ port .v9
private def direct : NetKAT := port .v0 ⨟ sw .v9 ⨟ write .v9

private def check (name : String) (p q : NetKAT) (expected : Bool) : IO Unit := do
  let actual := netkatNativeEquiv p q
  unless actual == expected do
    throw (IO.userError s!"{name}: expected {expected}, got {actual}")

#eval do
  check "drop" .drop (.test .pFalse) true
  check "identity" .id (.test .pTrue) true
  check "overwrite" (write .v1 ⨟ write .v8) (write .v8) true
  check "assignment commutation" (write .v1 ⨟ sw .v9) (sw .v9 ⨟ write .v1) true
  check "field contradiction" (port .v1 ⨟ port .v8) .drop true
  check "matching posttest" (write .v1 ⨟ port .v1) (write .v1) true
  check "matching pretest" (port .v1 ⨟ write .v1) (port .v1) true
  check "different-field test/update commutation" (port .v8 ⨟ sw .v9) (sw .v9 ⨟ port .v8) true
  check "field exhaustiveness" (port .v0 ∔ port .v1 ∔ port .v8 ∔ port .v9) .id true
  check "Boolean guard" (.test protectedInput)
    (.test (.pAnd (.fieldEq .tpSrc .v8) (.pNot (.fieldEq .port .v1)))) true
  check "complete test" (.completeTest examplePacket)
    (NetKAT.fieldTest .tpSrc .v8 ⨟ NetKAT.fieldTest .tpDst .v0 ⨟
     NetKAT.fieldTest .swId .v0 ⨟ port .v0) true
  check "firewall distribution and overwrite"
    ((firewall ∔ (firewall ⨟ .test .pFalse)) ⨟ write .v8)
    (.test protectedInput ⨟ write .v8 ⨟ sw .v9) true
  check "union associativity" ((port .v0 ∔ port .v1) ∔ port .v8)
    (port .v0 ∔ (port .v1 ∔ port .v8)) true
  check "sequence distributes over union" ((port .v0 ∔ port .v1) ⨟ write .v8)
    ((port .v0 ⨟ write .v8) ∔ (port .v1 ⨟ write .v8)) true
  check "right star unfold" (.star (write .v1)) (.id ∔ (.star (write .v1) ⨟ write .v1)) true
  check "star inequivalence" (.star (write .v1)) (.star (write .v8)) false
  check "mismatching assignments" (write .v1) (write .v8) false
  check "incompatible tests" (port .v1) (port .v8) false
  check "missing left test" firewall (write .v1 ⨟ sw .v9) false
  unless sat (distinguishingGuard firewall (write .v1 ⨟ sw .v9)).1 do
    throw (IO.userError "expected a satisfiable firewall counterexample")

private def branchNodes : Diagram n → Nat
  | .leaf _ => 0
  | .skip d => branchNodes d
  | .node l r => 1 + branchNodes l + branchNodes r

private def measure (name : String) (p q : NetKAT) : IO Unit := do
  let start ← IO.monoNanosNow
  let g := compileSymbolic p
  let h := compileSymbolic q
  unless compareOutputGuards g h do throw (IO.userError s!"unexpected inequality in {name}")
  let stop ← IO.monoNanosNow
  let a : Expr (Fin symbolicSchema.width) Empty := .test (g.1.toTest id)
  let b : Expr (Fin symbolicSchema.width) Empty := .test (h.1.toTest id)
  IO.println s!"{name}: guard nodes {nodes g.1}/{nodes h.1}, branch nodes {branchNodes g.1}/{branchNodes h.1}, native supports {(support a).card}/{(support b).card}, explored pairs {(explored a b).card}, {(stop - start) / 1000} us"

#eval measure "overwrite" (write .v1 ⨟ write .v8) (write .v8)
#eval measure "nested-star route" route direct

open Lean in
private partial def dependencies (env : Environment) (pending : List Name)
    (seen : Std.HashSet Name := {}) : Std.HashSet Name :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then dependencies env rest seen
    else
      let body := (env.find? name).bind ConstantInfo.value?
      let next := (body.map Lean.Expr.getUsedConstants).getD #[] |>.toList.filter fun n =>
        n.toString.startsWith "KATLean." || n.toString.startsWith "DyNetKAT.NetKAT." ||
        n.toString.startsWith "_private.KATLean." || n.toString.startsWith "_private.DyNetKAT."
      dependencies env (next ++ rest) (seen.insert name)

open Lean in
run_cmd do
  let env ← getEnv
  for n in [`DyNetKAT.NetKAT.netkatEquiv, `DyNetKAT.NetKAT.execute,
      `DyNetKAT.NetKAT.packetList, `DyNetKAT.NetKAT.katchSemantics,
      `KATLean.Native.Explicit.decideLanguageEquiv] do
    if env.contains n then throwError "unexpected symbolic solver import: {n}"
  let used := dependencies env [``netkatNativeEquiv_correct]
  for n in [``decideEquiv_complete, ``netkatNativeEquiv_eq_solver, ``compareOutputGuards,
      ``compileSymbolic_correct, ``katInterp_correct,
      ``KATLean.NetKAT.Symbolic.Schema.seq_correct, ``KATLean.NetKAT.Guard.eval_project,
      ``KATLean.NetKAT.Symbolic.Schema.star_correct] do
    unless used.contains n do throwError "proof dependency missing: {n}"
  for n in [``ctxPkt_card, `DyNetKAT.NetKAT.instFintypeCtxPkt] do
    if used.contains n then throwError "concrete enumeration dependency: {n}"

#print axioms KATLean.NetKAT.Symbolic.Schema.fieldTest_correct
#print axioms KATLean.NetKAT.Symbolic.Schema.assign_correct
#print axioms KATLean.NetKAT.Symbolic.Schema.primitive_correct
#print axioms KATLean.NetKAT.Symbolic.Schema.seq_correct
#print axioms KATLean.NetKAT.Symbolic.Schema.star_correct
#print axioms compilePredicate_correct
#print axioms compile_test_correct
#print axioms compile_assign_correct
#print axioms compile_completeTest_correct
#print axioms compileSymbolic_correct
#print axioms compileNative_correct
#print axioms netkatNativeEquiv_sound
#print axioms netkatNativeEquiv_complete
#print axioms netkatNativeEquiv_correct
#print axioms distinguishingGuard_sat

end SymbolicNetKATTests
