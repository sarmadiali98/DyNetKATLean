import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.MemoProjectionTests

open DyNetKAT.NetKAT

private def graph : ProcessGraph where
  nodes := ∅
  root := .deadlock
  label := fun _ => .deadlock
  root_closed := by simp [gprocRefs]
  closed := by simp

private def allowAll : RestrictionChecks := fun _ _ => false
private def send : GProc := .send "sync" .id (.rcfgPrefix "later" .id .deadlock)
private def recv : GProc := .recv "sync" .id .deadlock
private def bodyChecks (_ : NodeId) : RestrictionChecks := allowAll

private def memo (n : Nat) (p : GProc) (checks : RestrictionChecks := allowAll) :=
  renderProjectionMemo graph bodyChecks n ⟨p, checks⟩

private def tree (n : Nat) (p : GProc) (checks : RestrictionChecks := allowAll) :=
  renderProjection graph bodyChecks n ⟨p, checks⟩

private def handshake : DyNetKAT := choiceOf [.rcfgPrefix "sync" .id .deadlock]

example : (memo 0 (.parallel send recv)).map Prod.fst = some .deadlock := rfl

example : (memo 1 (.nSeq .id .deadlock)).map Prod.fst =
    some (choiceOf [.nSeq .id .deadlock]) := rfl

example : (memo 1 (.parallel send recv)).map Prod.fst = tree 1 (.parallel send recv) := rfl

example : (memo 1 (.restrict Set.univ (.restrict ∅ (.parallel send recv)))
    (fun path _ => path.isEmpty)).map Prod.fst = some handshake := rfl

example : (memo 1 (.restrict Set.univ (.parallel recv send))
    (fun _ _ => true)).map Prod.fst = some handshake := rfl

example : (memo 2 (.leftMerge (.rcfgPrefix "go" .id .deadlock) (.restrict Set.univ send))
    (fun path _ => path == [true])).map Prod.fst =
    some (choiceOf [.rcfgPrefix "go" .id .deadlock]) := rfl

example : (memo 1 (.commMerge recv send)).map Prod.fst = some handshake := rfl

example : (memo 3 (.project 1 (.project 2 (.commMerge send recv)))).map Prod.fst =
    some handshake := rfl

private def sharedTail : GProc := .rcfgPrefix "tail" .id (.nSeq .id .deadlock)
private def repeated : GProc :=
  .choice (.rcfgPrefix "left" .id sharedTail) (.rcfgPrefix "right" .id sharedTail)

private def noCache (n : Nat) (p : GProc) :=
  renderProjectionMemoWith (.disabled graph bodyChecks) n ⟨p, allowAll⟩

-- Both branches request sharedTail at depth 2. There is a positive-depth
-- hit, and the second request skips both child calls of that subtree.
#guard (memo 3 repeated).map Prod.snd == some ⟨1, 4, 2⟩
#guard (noCache 3 repeated).map Prod.snd == some ⟨0, 7, 0⟩

example : (memo 3 repeated).map Prod.fst = (noCache 3 repeated).map Prod.fst := rfl

-- The same process appears at depths 2 and 1. The second rendering must
-- retain one fewer prefix even though the process part of the key matches.
private def differentDepths : GProc :=
  .choice (.rcfgPrefix "left" .id sharedTail)
    (.rcfgPrefix "right" .id (.rcfgPrefix "delay" .id sharedTail))

example : (memo 3 differentDepths).map Prod.fst = tree 3 differentDepths := rfl

-- Opaque restriction states are recomputed. The two sibling residuals
-- intentionally have different restriction sets and classifier values.
private def differentRestrictions : GProc :=
  .choice (.rcfgPrefix "left" .id (.restrict Set.univ recv))
    (.rcfgPrefix "right" .id (.restrict ∅ recv))

#guard (memo 2 differentRestrictions (fun path _ => path == [false, false])).map Prod.snd ==
  some ⟨0, 4, 0⟩

example : (memo 2 differentRestrictions (fun path _ => path == [false, false])).map Prod.fst =
    some (choiceOf [.rcfgPrefix "left" .id .deadlock,
      .rcfgPrefix "right" .id (choiceOf [.recv "sync" .id .deadlock])]) := rfl

private def node : NodeId := varNode "Loop"
private def refGraph : ProcessGraph where
  nodes := {node}
  root := .ref node
  label := fun _ => .rcfgPrefix "open" .id (.restrict Set.univ (.send "sync" .id (.ref node)))
  root_closed := by simp [gprocRefs]
  closed := by simp [gprocRefs]

-- Looking up a memoized reference is independent of the root classifier,
-- but the newly exposed restriction uses the classifier of the body.
example : (renderProjectionMemo refGraph (fun _ path _ => path == [false])
    2 ⟨refGraph.root, allowAll⟩).map Prod.fst =
    some (choiceOf [.rcfgPrefix "open" .id .deadlock]) := rfl

#print axioms ProjectionMemoKey.prefixKey_proc
#print axioms ProjectionMemoKey.prefixChain_checks
#print axioms ProjectionMemoKey.prefixChains
#print axioms ProjectionMemo.valid_empty
#print axioms ProjectionMemo.lookup_correct
#print axioms ProjectionMemo.insert_valid
#print axioms ProjectionMemo.run_correct
#print axioms renderProjectionMemo_eq
#print axioms renderProjectionMemo_bisimilar
#print axioms renderProjectionMemo_source
#print axioms renderProjectionMemo_restricted

end DyNetKAT.DyNetKAT.MemoProjectionTests
