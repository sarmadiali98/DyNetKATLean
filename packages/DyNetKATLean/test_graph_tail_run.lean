import DyNetKATLean

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.GraphTailRunTests

open DyNetKAT.NetKAT

private abbrev x : NodeId := varNode "X"
private abbrev y : NodeId := varNode "Y"
private abbrev z : NodeId := varNode "Z"

-- Scenario 1: X ≜ N;X
private abbrev selfLoop := exSelfLoopGraph NetKAT.id

example : tailRefsR ∅ selfLoop.root = [x] := rfl
example : tailRefsR ∅ (selfLoop.label x) = [x] := rfl

example : tailRun selfLoop ∅ (tailRefsR ∅ selfLoop.root) ∅ [] = some [x] := by
  simp [tailRun, tailRefsR, exSelfLoopGraph, exSelfLoopLabel, varNode]

-- Scenario 5: X ≜ rcfg_a; N; rcfg_b; X
private def syncBody : GProc :=
  .rcfgPrefix "a" .id (.nSeq .id (.rcfgPrefix "b" .id (.ref x)))

private def syncCycle : ProcessGraph where
  nodes := {x}
  root := .ref x
  label := fun _ => syncBody
  root_closed := by simp [gprocRefs]
  closed := by simp [syncBody, gprocRefs]

private abbrev bothEvents : ReconfigSet := {("a", NetKAT.id), ("b", NetKAT.id)}
private abbrev firstEvent : ReconfigSet := {("a", NetKAT.id)}

example : tailRefsR bothEvents (syncCycle.label x) = [x] := rfl
example : tailRefsR firstEvent (syncCycle.label x) = [] := rfl
example : tailRefsR {("b", NetKAT.id)} (syncCycle.label x) = [] := rfl

example : tailRun syncCycle bothEvents (tailRefsR bothEvents syncCycle.root) ∅ [] =
    some [x] := by
  have hRefs : tailRefsR bothEvents syncBody = [x] := rfl
  simp [tailRun, tailRefsR, syncCycle, hRefs]

#eval tailRun syncCycle bothEvents (tailRefsR bothEvents syncCycle.root) ∅ []

-- Scenario 6: adding the unreachable Z ≜ N;Z does not change the worklist.
private abbrev withUnreachable := exUnreachableGraph NetKAT.id

private def withoutUnreachable : ProcessGraph where
  nodes := {x}
  root := withUnreachable.root
  label := withUnreachable.label
  root_closed := by simp [exUnreachableGraph, gprocRefs]
  closed := by
    intro i hi
    have hiX : i = x := Finset.mem_singleton.mp hi
    subst i
    simp [exUnreachableGraph, exUnreachableLabel, gprocRefs, varNode]

example : tailRefsR bothEvents (withUnreachable.label z) = [z] := rfl

example : tailRun withUnreachable bothEvents (tailRefsR bothEvents withUnreachable.root) ∅ [] =
    some [x] := by
  simp [tailRun, tailRefsR, exUnreachableGraph, exUnreachableLabel, varNode]

example : tailRun withoutUnreachable bothEvents
    (tailRefsR bothEvents withoutUnreachable.root) ∅ [] = some [x] := by
  simp [tailRun, tailRefsR, withoutUnreachable, exUnreachableGraph, exUnreachableLabel, varNode]

-- Scenario 7: X ≜ Y and Y ≜ X
example : tailRefsR ∅ (exUnguardedGraph.label x) = [y] := rfl
example : tailRefsR ∅ (exUnguardedGraph.label y) = [x] := rfl

private theorem unguardedRun :
    tailRun exUnguardedGraph ∅ (tailRefsR ∅ exUnguardedGraph.root) ∅ [] = some [y, x] := by
  simp [tailRun, tailRefsR, exUnguardedGraph, exUnguardedLabel, varNode]

example : ([y, x] : List NodeId).Nodup :=
  (tailRun_root_success exUnguardedGraph ∅ [y, x] unguardedRun).1

#eval tailRun exUnguardedGraph ∅ (tailRefsR ∅ exUnguardedGraph.root) ∅ []

-- ProcessGraph closure excludes dangling references in roots and live
-- labels. Seed the worklist from a standalone term to exercise failure.
private def dangling : GProc := .rcfgPrefix "a" .id (.ref (varNode "missing"))
private abbrev wrongPolicy : ReconfigSet := {("a", NetKAT.drop)}

example : tailRefsR wrongPolicy dangling = [] := rfl
example : tailRefsR firstEvent dangling = [varNode "missing"] := rfl

example : tailRun selfLoop wrongPolicy (tailRefsR wrongPolicy dangling) ∅ [] =
    some [] := by
  rw [show tailRefsR wrongPolicy dangling = [] from rfl, tailRun.eq_1]

example : tailRun selfLoop firstEvent (tailRefsR firstEvent dangling) ∅ [] =
    none := by
  rw [show tailRefsR firstEvent dangling = [varNode "missing"] from rfl]
  simp [tailRun, exSelfLoopGraph, varNode]

#eval tailRun selfLoop wrongPolicy (tailRefsR wrongPolicy dangling) ∅ []
#eval tailRun selfLoop firstEvent (tailRefsR firstEvent dangling) ∅ []

#print axioms tailRefsR
#print axioms mem_tailRefsR_iff
#print axioms tailRefsR_subset_gprocRefs
#print axioms TailRefOf
#print axioms TailRefReach
#print axioms TailPathTo
#print axioms tailPathTo_iff
#print axioms tailRefReach_iff_tailPathTo
#print axioms tailPathTo_step
#print axioms tailPathTo_nodes_closed
#print axioms tailRun
#print axioms tailRun_spec
#print axioms tailRun_root_success
#print axioms tailRun_root_failure
#print axioms tailRun_root_some

end DyNetKAT.DyNetKAT.GraphTailRunTests
