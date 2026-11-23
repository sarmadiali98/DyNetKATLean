import DyNetKATLean

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.RestrictionMovesTests

open DyNetKAT.NetKAT

private def send : GProc := .send "sync" .id .deadlock
private def recv : GProc := .recv "sync" .id .deadlock
private def joint : GProc := .parallel .deadlock .deadlock
private def syncLabel : MoveLabel := .visible (.rcfg "sync" .id)
private def blockAll : RestrictionChecks := fun _ _ => true
private def moves (p : GProc) (checks : RestrictionChecks := blockAll) :=
  localMoves (fun _ => none) p (some checks)

private theorem allCorrect (c : CommunicationAction) :
    blockAll [] c = true ↔ c ∈ (Set.univ : Set CommunicationAction) := by
  simp [blockAll]

-- Filtering the completed parallel row removes both unilateral moves.
example : moves (.restrict Set.univ (.parallel send recv)) =
    some [(syncLabel, .restrict Set.univ joint)] := rfl

example : moves (.restrict Set.univ (.parallel recv send)) =
    some [(syncLabel, .restrict Set.univ joint)] := rfl

-- Filtering the operands first suppresses the handshake.
example : moves (.parallel (.restrict Set.univ send) (.restrict Set.univ recv)) =
    some [] := rfl

-- These concrete rows account for exactly one SOS step, with both packet lists unchanged.
example (G : ProcessGraph) (pt hl : List CtxPkt) :
    GStep G ⟨.restrict Set.univ (.parallel send recv), pt, hl⟩ (.rcfg "sync" .id)
      ⟨.restrict Set.univ joint, pt, hl⟩ := by
  have he : MovesExact G (.restrict Set.univ (.parallel send recv))
      [(syncLabel, .restrict Set.univ joint)] :=
    localMoves_exact_with (atRef := fun _ => True) (checks := some blockAll) (by simp)
      ⟨allCorrect, trivial, trivial⟩ (show moves _ = some _ from rfl)
  exact (he ..).mpr ⟨_, by simp [syncLabel], .rcfg⟩

example (G : ProcessGraph) (pt hl : List CtxPkt) :
    GStep G ⟨.restrict Set.univ (.parallel recv send), pt, hl⟩ (.rcfg "sync" .id)
      ⟨.restrict Set.univ joint, pt, hl⟩ := by
  have he : MovesExact G (.restrict Set.univ (.parallel recv send))
      [(syncLabel, .restrict Set.univ joint)] :=
    localMoves_exact_with (atRef := fun _ => True) (checks := some blockAll) (by simp)
      ⟨allCorrect, trivial, trivial⟩ (show moves _ = some _ from rfl)
  exact (he ..).mpr ⟨_, by simp [syncLabel], .rcfg⟩

-- Two nested sites have different membership tests. The inner test blocks the
-- send, and the outer test permits the receive. Both wrappers survive.
private def blocked : Finset CommunicationAction := {.send "sync" .id}
private def nestedChecks : RestrictionChecks
  | [false], c => decide (c ∈ blocked)
  | _, _ => false

private def nested : GProc := .restrict ∅
  (.restrict (↑blocked : Set CommunicationAction) (.choice send recv))
private def nestedRow : List SymbolicMove :=
  [(.recv "sync" .id, .restrict ∅ (.restrict (↑blocked : Set CommunicationAction) .deadlock))]

private theorem nestedComputed : moves nested nestedChecks = some nestedRow := rfl

example (G : ProcessGraph) : MovesExact G nested nestedRow := by
  apply localMoves_exact_with (atRef := fun _ => True) (by simp) _ nestedComputed
  simp [nested, RestrictionChecksCorrect, RestrictionChecks.child, nestedChecks, send, recv]

example : moves (.restrict Set.univ (.project 1 (.parallel recv send))) =
    some [(syncLabel, .restrict Set.univ (.project 0 joint))] := rfl

example : moves (.restrict Set.univ (.project 0 joint)) = some [] := rfl

example : moves (.project 1 (.restrict Set.univ (.commMerge send recv))) =
    some [(syncLabel, .project 0 (.restrict Set.univ joint))] := rfl

example : moves (.restrict Set.univ (.leftMerge send recv)) = some [] := rfl

example : moves (.restrict Set.univ (.nSeq .id .deadlock)) =
    some [(.visible (.packet .id), .restrict Set.univ .deadlock)] := rfl

-- A restriction encountered after lookup uses the definition's classifier,
-- independent of the classifier supplied for the root.
private def name : NodeId := varNode "Guarded"
private def bodyGraph : ProcessGraph where
  nodes := {name}
  root := .ref name
  label := fun _ => .restrict (↑blocked : Set CommunicationAction)
    (.choice send (.recv "sync" .id (.ref name)))
  root_closed := by simp [gprocRefs]
  closed := by simp [gprocRefs, send]

private def definitionChecks (_ : NodeId) : Option RestrictionChecks :=
  some (fun _ c => decide (c ∈ blocked))

private def bodyRow : List SymbolicMove :=
  [(.recv "sync" .id, .restrict (↑blocked : Set CommunicationAction) (.ref name))]

private theorem bodyComputed :
    guardedMoves bodyGraph bodyGraph.root (some blockAll) definitionChecks = some bodyRow := rfl

example : MovesExact bodyGraph bodyGraph.root bodyRow := by
  apply guardedMoves_exact_with _ bodyComputed
  simp [GuardedRestrictionChecksCorrect, RestrictionChecksCorrect, bodyGraph,
    definitionChecks, RestrictionChecks.child, send]

#guard (moves (.restrict Set.univ (.parallel send recv))).map List.length == some 1

#print axioms MovesExact.restrict
#print axioms localMoves_exact_with

end DyNetKAT.DyNetKAT.RestrictionMovesTests
