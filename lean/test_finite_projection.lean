import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.FiniteProjectionTests

open DyNetKAT.NetKAT

private def graph : ProcessGraph where
  nodes := ∅
  root := .deadlock
  label := fun _ => .deadlock
  root_closed := by simp [gprocRefs]
  closed := by simp

private def allowAll : RestrictionChecks := fun _ _ => false
private def blockAll : RestrictionChecks := fun _ _ => true
private def send : GProc := .send "sync" .id (.rcfgPrefix "later" .id .deadlock)
private def recv : GProc := .recv "sync" .id .deadlock
private def handshake : DyNetKAT := choiceOf [.rcfgPrefix "sync" .id .deadlock]

private def render (n : Nat) (p : GProc) (checks : RestrictionChecks := allowAll) :=
  renderProjection graph (fun _ => allowAll) n ⟨p, checks⟩

example : render 0 (.parallel send recv) = some .deadlock := rfl

example : render 0 (.restrict Set.univ (.commMerge send recv)) = some .deadlock := rfl

example : render 1 (.nSeq .id (.rcfgPrefix "later" .id .deadlock)) =
    some (choiceOf [.nSeq .id .deadlock]) := rfl

example : render 1 (.restrict Set.univ (.parallel send recv)) blockAll = some handshake := rfl

example : render 1 (.restrict Set.univ (.parallel recv send)) blockAll = some handshake := rfl

example (env : RecEnv) (pt hl : List CtxPkt) :
    Step env ⟨handshake, pt, hl⟩ (.rcfg "sync" .id) ⟨.deadlock, pt, hl⟩ ∧
    ∀ a d, ¬ Step env ⟨.deadlock, pt, hl⟩ a d := by
  exact ⟨.cpol_choice_l _ _ _ _ _ _ _ _ (.cpol_rcfg _ _ _ _ _),
    fun a d => deadlock_no_step env pt hl a d⟩

-- The outer site blocks everything and the inner site allows everything.
-- The handshake is already a reconfiguration by the time either filters it.
example : render 1 (.restrict Set.univ (.restrict ∅ (.parallel send recv)))
    (fun path _ => path.isEmpty) = some handshake := rfl

-- The restriction is dormant until the first step. The left merge also
-- changes to parallel, retaining the classifier of its passive operand.
example : render 2 (.leftMerge (.rcfgPrefix "go" .id .deadlock) (.restrict Set.univ send))
    (fun path _ => path == [true]) = some (choiceOf [.rcfgPrefix "go" .id .deadlock]) := rfl

example : render 2 (.rcfgPrefix "go" .id (.restrict Set.univ send))
    (fun path _ => path == [false]) = some (choiceOf [.rcfgPrefix "go" .id .deadlock]) := rfl

example : render 1 (.commMerge recv send) = some handshake := rfl

example : render 3 (.project 1 (.project 2 (.commMerge send recv))) = some handshake := rfl

example : render 3 (.project 0 (.commMerge send recv)) = some .deadlock := rfl

private def guardedNode : NodeId := varNode "Guarded"

private def delayedRestrictionGraph : ProcessGraph where
  nodes := {guardedNode}
  root := .ref guardedNode
  label := fun _ => .rcfgPrefix "open" .id
    (.restrict Set.univ (.send "sync" .id (.ref guardedNode)))
  root_closed := by simp [gprocRefs]
  closed := by simp [gprocRefs]

-- A root lookup consumes no depth. The continuation uses the definition's
-- classifier at its original child path, despite the root allowing sends.
example : renderProjection delayedRestrictionGraph
    (fun _ path _ => path == [false]) 2 ⟨delayedRestrictionGraph.root, allowAll⟩ =
    some (choiceOf [.rcfgPrefix "open" .id .deadlock]) := rfl

#print axioms checkedMoves_spec
#print axioms GSteps.checkedResidual
#print axioms Steps.checkedResidual
#print axioms renderProjection_exists
#print axioms renderProjection_closed
#print axioms renderProjectionTotal
#print axioms renderProjection_bisimilar
#print axioms renderProjection_source
#print axioms renderProjection_restricted

end DyNetKAT.DyNetKAT.FiniteProjectionTests
