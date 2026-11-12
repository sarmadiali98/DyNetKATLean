import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.TypedGuardednessTests

example (x : Var) : ¬ TypedPaperGuarded (.var x) :=
  fun h => h x .here

example (x : Var) : ProcessVarOccurrence (.nSeq .id (.var x)) x true := .packet .here
example (x : Var) : TypedPaperGuarded (.nSeq .id (.var x)) := by intro _ h; cases h
example (x : Var) : TypedPaperGuarded (.send "c" .id (.var x)) := by intro _ h; cases h
example (x : Var) : TypedPaperGuarded (.recv "c" .id (.var x)) := by intro _ h; cases h
example (x : Var) : TypedPaperGuarded (.rcfgPrefix "c" .id (.var x)) := by intro _ h; cases h

example (x : Var) (L : Set CommunicationAction) :
    ¬ TypedPaperGuarded (.restrict L (.var x)) :=
  fun h => h x (.restrict .here)

example (x : Var) (n : Nat) : ¬ TypedPaperGuarded (.project n (.var x)) :=
  fun h => h x (.project .here)

example (p q : DyNetKAT) :
    TypedPaperGuarded (.leftMerge p q) ↔ TypedPaperGuarded p ∧ TypedPaperGuarded q := by
  simp only [typedPaperGuarded_iff_guardedOccurrences, GuardedOccurrences]

example : ¬ TypedPaperGuarded (.parallel (.var "Host") .deadlock) :=
  fun h => h "Host" (.parallelLeft .here)

example : ¬ TypedPaperGuarded (.commMerge .deadlock (.var "Switch")) :=
  fun h => h "Switch" (.commMergeRight .here)

-- The payload and channel positions cannot accept process ASTs.
example : True := by
  fail_if_success have bad := DyNetKAT.recv "c" (DyNetKAT.var "X") .deadlock
  fail_if_success have bad := DyNetKAT.send "c" (DyNetKAT.var "X") .deadlock
  fail_if_success have bad := DyNetKAT.rcfgPrefix "c" (DyNetKAT.var "X") .deadlock
  fail_if_success have bad := DyNetKAT.rcfgPrefix (DyNetKAT.var "X") .id .deadlock
  trivial

private def cycle : RecEnv := RecEnv.empty.define "X" (.var "X")

example : ClosedDefined cycle (.var "X") := by
  have onlyX (x : Var) (hx : ReachableVar cycle (.var "X") x) : x = "X" := by
    induction hx with
    | direct occurs => simpa using occurs
    | throughDefinition _ lookup occurs ih =>
      subst ih
      have hb := RecEnv.lookup_unique (env := cycle) (x := "X")
        (p := .var "X") rfl lookup
      cases hb
      simpa using occurs
  intro x hx
  rw [onlyX x hx]
  rfl

example : ¬ WellFormed cycle (.var "X") := by
  intro h
  have guard := h.reachable_guarded cycle (.var "X") "X" (.var "X") (.direct (by simp)) rfl
  exact not_guardedOccurrences_var "X" guard

#print axioms typedPaperGuarded_iff_guardedOccurrences
#print axioms RecEnv.lookup_unique
#print axioms ClosedDefined.existsUnique_lookup
#print axioms wellFormed_iff_closedDefined_and_typedPaperGuarded

end DyNetKAT.DyNetKAT.TypedGuardednessTests
