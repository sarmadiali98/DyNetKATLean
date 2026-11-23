import DyNetKATLean

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.GraphTailAssemblyTests

open DyNetKAT.NetKAT

private abbrev x : NodeId := varNode "X"
private abbrev y : NodeId := varNode "Y"
private abbrev z : NodeId := varNode "Z"
private abbrev allowA : ReconfigSet := {("a", NetKAT.id)}
private abbrev allowAB : ReconfigSet := {("a", NetKAT.id), ("b", NetKAT.id)}

private def graphWithoutRefs (root : GProc) (h : gprocRefs root = ∅) : ProcessGraph where
  nodes := ∅
  root := root
  label := fun _ => .deadlock
  root_closed := by rw [h]
  closed := by simp

private def simple := graphWithoutRefs (.rcfgPrefix "a" .id (.nSeq .id .deadlock)) rfl
private def tailHeadEquiv (G : ProcessGraph) (R : ReconfigSet) (policy : NetKAT) : Bool :=
  match (graphTail G R).bind graphHead with
  | some headPolicy => netkatEquiv headPolicy policy
  | none => false

#guard tailHeadEquiv simple allowA .id
#guard tailHeadEquiv (exSelfLoopGraph .id) ∅ .drop
#guard tailHeadEquiv (exMutualGraph .id .id) ∅ .drop

example : ∃ G', graphTail simple allowA = some G' := by
  apply graphTail_supported_some
  refine ⟨.rcfgPrefix (.nSeq .deadlock), ?_⟩
  simp [simple, graphWithoutRefs, gprocRefs]

-- A later policy can contribute only when both reconfigurations match.
private def laterPolicy : NetKAT := .fieldTest .port .v8
private def multiple := graphWithoutRefs
  (.rcfgPrefix "a" .id (.nSeq .drop (.rcfgPrefix "b" .id (.nSeq laterPolicy .deadlock)))) rfl

#guard tailHeadEquiv multiple allowAB laterPolicy
#guard tailHeadEquiv multiple allowA .drop

private def barrier := graphWithoutRefs
  (.rcfgPrefix "a" .id (.recv "ctrl" .id .deadlock)) rfl
private abbrev wrongPolicy : ReconfigSet := {("a", NetKAT.drop)}

#guard tailHeadEquiv barrier wrongPolicy .drop
#guard (graphTail barrier allowA).isNone
-- This failure is in a visited label; the root collection itself succeeds.
#guard (graphTail (exRcfgGraph "a" .id) allowA).isNone
#guard tailHeadEquiv (exRcfgGraph "a" .id) wrongPolicy .drop

-- A verbatim branch can retain unsupported syntax behind a barrier.
private def nestedBarrier := graphWithoutRefs
  (.rcfgPrefix "a" .id
    (.nSeq .id (.rcfgPrefix "b" .id (.recv "ctrl" .id .deadlock)))) rfl

#guard tailHeadEquiv nestedBarrier allowA .id
#guard (graphTail nestedBarrier allowAB).isNone

example : GraphTailDomain barrier wrongPolicy := by
  have hrun : tailRun barrier wrongPolicy (tailRefsR wrongPolicy barrier.root) ∅ [] =
      some [] := tailRun.eq_1 ..
  have hroot : tailCollectR barrier wrongPolicy (fresh barrier []) barrier.root =
      some .deadlock := rfl
  have h := graphTail_eq_some_tailGraphOf hrun hroot rfl
  exact graphTail_domain_iff.mpr ⟨_, h⟩

example : ¬ GraphTailSupported barrier := by
  intro h
  have hshape := h.1
  change TailShapeOk barrier (.rcfgPrefix "a" .id (.recv "ctrl" .id .deadlock)) at hshape
  cases hshape with
  | rcfgPrefix hcont => cases hcont

private abbrev mutualGraph := exMutualGraph NetKAT.id NetKAT.id
private theorem mutualRun :
    tailRun mutualGraph ∅ (tailRefsR ∅ mutualGraph.root) ∅ [] = some [y, x] := by
  simp [tailRun, tailRefsR, exMutualGraph, exMutualLabel, varNode]

private def mutualOut : ProcessGraph :=
  tailGraphOf mutualGraph ∅ [y, x] (.ref (auxNode 2))
    [(y, .ref (auxNode 2)), (x, .ref (auxNode 1))] mutualRun rfl rfl

example : graphTail mutualGraph ∅ = some mutualOut :=
  graphTail_eq_some_tailGraphOf mutualRun rfl rfl

example : mutualOut.label (auxNode 1) = .ref (auxNode 2) :=
  tailGraphOf_label_fresh (show y ∈ [y, x] by simp) rfl

example : mutualOut.label (auxNode 2) = .ref (auxNode 1) :=
  tailGraphOf_label_fresh (show x ∈ [y, x] by simp) rfl

-- Audit §5.11, with an unreachable unsupported recursive definition Z
-- and an existing auxiliary identifier.
private def matchingCont : GProc := .nSeq .id (.ref x)
private def blockedCont : GProc := .nSeq .drop (.ref x)
private def counterBody : GProc :=
  .choice (.rcfgPrefix "a" .id matchingCont) (.rcfgPrefix "c" .id blockedCont)
private def unreachableBody : GProc :=
  .choice (.recv "ctrl" .id .deadlock) (.ref z)

private def counterGraph : ProcessGraph where
  nodes := {x, z, auxNode 7}
  root := .ref x
  label := fun i => if i = x then counterBody else if i = z then unreachableBody else .deadlock
  root_closed := by simp [gprocRefs]
  closed := by
    intro i _ k hk
    split at hk
    · have he : k = x := by simpa [counterBody, matchingCont, blockedCont, gprocRefs] using hk
      simp [he]
    · split at hk
      · have he : k = z := by simpa [unreachableBody, gprocRefs] using hk
        simp [he]
      · simp [gprocRefs] at hk

private theorem counterRun :
    tailRun counterGraph allowA (tailRefsR allowA counterGraph.root) ∅ [] = some [x] := by
  have hrefs : tailRefsR allowA (counterGraph.label x) = [x] := rfl
  have hroot : tailRefsR allowA counterGraph.root = [x] := rfl
  rw [hroot, tailRun.eq_2, dif_neg (Finset.not_mem_empty x)]
  have hx : x ∈ counterGraph.nodes := by simp [counterGraph]
  rw [dif_pos hx, hrefs]
  simp [tailRun]

private def collectedBody : GProc :=
  .choice (.choice matchingCont (.ref (auxNode 8))) .deadlock

private def assembled : ProcessGraph :=
  tailGraphOf counterGraph allowA [x] (.ref (auxNode 8)) [(x, collectedBody)] counterRun rfl rfl

private theorem counterTail : graphTail counterGraph allowA = some assembled :=
  graphTail_eq_some_tailGraphOf counterRun rfl rfl

example : assembled.nodes = {x, z, auxNode 7, auxNode 8} := by decide
example : assembled.root = .ref (auxNode 8) := rfl
example (i : NodeId) (hi : i ∈ counterGraph.nodes) :
    assembled.label i = counterGraph.label i := tailGraphOf_label_original hi
example : assembled.label (auxNode 8) = collectedBody :=
  tailGraphOf_label_fresh (show x ∈ [x] by simp) rfl
example : Disjoint counterGraph.nodes (([x] : List NodeId).toFinset.image
    (fresh counterGraph [x])) := by decide
example : assembled.label (auxNode 9) = .deadlock :=
  tailGraphOf_label_outside (by decide)
private theorem assembled_root_closed : gprocRefs assembled.root ⊆ assembled.nodes :=
  assembled.root_closed
private theorem assembled_closed : ∀ i ∈ assembled.nodes, gprocRefs (assembled.label i) ⊆ assembled.nodes :=
  assembled.closed
example : ∃ H, graphHead assembled = some H := graphTail_head_some counterTail

-- After the verbatim packet continuation returns to X, it can still
-- take the original c step, even though c was cut during collection.
example (σ : CtxPkt) :
    GStep assembled ⟨.ref x, [], [σ]⟩ (.rcfg "c" .id) ⟨blockedCont, [], [σ]⟩ := by
  apply GStep.var
  have hx : x ∈ counterGraph.nodes := by simp [counterGraph]
  have hlabel : assembled.label x = counterBody := tailGraphOf_label_original hx
  change GStep assembled ⟨assembled.label x, [], [σ]⟩ _ _
  rw [hlabel]
  exact .choice_r _ _ _ _ _ _ _ _ (.rcfg "c" .id blockedCont [] [σ])

#guard tailHeadEquiv counterGraph allowA .id
#eval (graphTail counterGraph allowA).map (fun G => G.nodes.card)
#eval (graphTail (exMutualGraph .id .id) ∅).map (fun G => G.nodes.card)
#eval (graphTail barrier allowA).isNone

#print axioms tailCollectR_refs_iff
#print axioms tailCollectR_refs_closed
#print axioms tailGraphOf
#print axioms tailGraphOf_nodes
#print axioms tailGraphOf_root
#print axioms tailGraphOf_label_original
#print axioms tailGraphOf_label_fresh
#print axioms tailGraphOf_label_outside
#print axioms assembled_root_closed
#print axioms assembled_closed
#print axioms graphTail
#print axioms graphTail_domain_some
#print axioms graphTail_domain_iff
#print axioms graphTailSupported_implies_domain
#print axioms graphTail_supported_some
#print axioms graphTail_head_some

end DyNetKAT.DyNetKAT.GraphTailAssemblyTests
