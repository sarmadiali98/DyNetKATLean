import KATLean.Native
import KATLean.Native.Explicit
import DyNetKAT.NetKAT.NativeEquations

open KATLean.Native
namespace SymbolicKATTests
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def x : Test (Fin 8) := .atom 0
private def y : Test (Fin 8) := .atom 7
#guard (Test.guard (.disj x (.neg x))) = (Boolean.truth : Guard (Fin 8))
#guard (Test.guard (.conj x (.neg x))) = (Boolean.falsity : Guard (Fin 8))
#guard (Test.guard (.neg (.conj x y))) = (Test.guard (.disj (.neg x) (.neg y)))
#guard (Test.guard (.neg (.disj x y))) = (Test.guard (.conj (.neg x) (.neg y)))
#guard Boolean.sat (Test.guard (.conj x (.neg y))).1
#guard !Boolean.sat (Test.guard (.conj x (.neg x))).1
-- Implication is unsatisfiability of the symbolic difference.
#guard !Boolean.sat (Boolean.conj (Test.guard (.conj x y)) (Boolean.neg x.guard)).1

private def a : Expr (Fin 8) (Fin 2) := .action 0
private def b : Expr (Fin 8) (Fin 2) := .action 1
#guard decideEquiv (.plus a a) a
#guard decideEquiv (.seq a (.plus a b)) (.plus (.seq a a) (.seq a b))
#guard decideEquiv (.plus .one (.seq a (.star a))) (.star a)
#guard decideEquiv (.star (.star a)) (.star a)
#guard decideEquiv (.star (.plus a b)) (.seq (.star a) (.star (.seq b (.star a))))
#guard decideEquiv (.seq (.test (.disj x (.neg x))) a) a
#guard !decideEquiv (.seq (.test x) a) (.seq (.test y) a)

private def allTests (n : Nat) : Test (Fin n) :=
  (List.ofFn (fun i : Fin n => Test.atom i)).foldr Test.conj .top
-- This alphabet has 2^64 assignments. Only a linear-size ordered diagram is built.
#guard Boolean.nodes (allTests 64).guard.1 = 129
#guard decideEquiv (A := Fin 1) (.test (.disj (allTests 64) (.neg (allTests 64)))) .one
#guard !decideEquiv (A := Fin 1) (.test (allTests 64)) .one
#guard decideEquiv (A := Fin 1)
  (.seq (.test (allTests 64)) (.plus .one (.action 0)))
  (.plus (.test (allTests 64)) (.seq (.test (allTests 64)) (.action 0)))

-- Differential oracle is test-only. Symbolic correctness never invokes it.
private def c : Expr (Fin 2) (Fin 2) := .action 0
private def d : Expr (Fin 2) (Fin 2) := .action 1
private def corpus : List (Expr (Fin 2) (Fin 2)) :=
  [.zero, .one, c, d, .test (.atom 0), .test (.neg (.atom 0)), .star c,
   .star (.star c), .plus c c, .seq (.test (.atom 0)) c,
   .plus .one (.seq c (.star c)), .star (.plus c d)]
#guard corpus.all (fun p => corpus.all (fun q => decideEquiv p q = Explicit.decideLanguageEquiv p q))

-- The proved algebraic direction, including its actual E_NK substitution bridge.
example : Equational (.plus a a) a := .plusIdem a
example : decideEquiv (.plus a a) a = true := (Equational.plusIdem a).solver_positive
example : AlgebraicallyEquivalent (.plus a a) a := (Equational.plusIdem a).algebraic_sound
example (actions : Fin 2 → DyNetKAT.NetKAT.NetKAT) (tests : Fin 8 → DyNetKAT.NetKAT.Predicate) :
    DyNetKAT.NetKAT.Derives
      (DyNetKAT.NetKAT.nativeEmbed actions tests (.plus a a))
      (DyNetKAT.NetKAT.nativeEmbed actions tests a) :=
  DyNetKAT.NetKAT.nativeEquational_derives (.plusIdem a) actions tests

private def testSize : Test T → Nat
  | .bot | .top | .atom _ => 1
  | .neg p => 1 + testSize p
  | .conj p q | .disj p q => 1 + testSize p + testSize q

private def size : Expr T A → Nat
  | .zero | .one | .action _ => 1
  | .test p => 1 + testSize p
  | .plus p q | .seq p q => 1 + size p + size q
  | .star p => 1 + size p

private def bench {n m : Nat} (label : String) (p q : Expr (Fin n) (Fin m)) : IO Unit := do
  let start ← IO.monoNanosNow
  let result := decideEquiv p q
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"{label}: equivalent={result}, exprNodes={size p + size q}, supportSizes={(support p).card}/{(support q).card}, pairs={(explored p q).card}, states={((explored p q).image Prod.fst).card}/{((explored p q).image Prod.snd).card}, outputGuardNodes={Boolean.nodes (outputGuard ({p} : State (Fin n) (Fin m))).1}/{Boolean.nodes (outputGuard ({q} : State (Fin n) (Fin m))).1}, initialRegions={((List.finRange m).map (fun action => (pairRegions (initial p q) action).length)).foldl (· + ·) 0}, nanos={elapsed}"

#eval bench "distributivity" (.seq a (.plus a b)) (.plus (.seq a a) (.seq a b))
#eval bench "denesting" (.star (.plus a b)) (.seq (.star a) (.star (.seq b (.star a))))
#eval bench (m := 1) "64-test partition"
  (.seq (.test (allTests 64)) (.plus .one (.action 0)))
  (.plus (.test (allTests 64)) (.seq (.test (allTests 64)) (.action 0)))

#print axioms Boolean.canonical
#print axioms Boolean.compile_correct
#print axioms Boolean.sat_correct
#print axioms derivativeRegions_correct
#print axioms transitionRegions_correct
#print axioms explored_closed
#print axioms decideEquiv_sound
#print axioms decideEquiv_complete
#print axioms Equational.algebraic_sound
#print axioms Equational.solver_positive
#print axioms DyNetKAT.NetKAT.nativeEquational_derives
end SymbolicKATTests
