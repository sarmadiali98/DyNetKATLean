import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.GraphTailCollectTests

open DyNetKAT.NetKAT

private abbrev x : NodeId := varNode "X"
private abbrev y : NodeId := varNode "Y"
private abbrev allowed : ReconfigSet := {("a", NetKAT.id)}

-- Audit §5.11: X ≜ rcfg_a; N; X ⊕ rcfg_c; M; X, with R = {a}.
private def matchingCont : GProc := .nSeq .id (.ref x)
private def blockedCont : GProc := .nSeq (.fieldTest .port .v8) (.ref x)
private def counterLabel : GProc :=
  .choice (.rcfgPrefix "a" .id matchingCont) (.rcfgPrefix "c" .id blockedCont)

private def counterGraph : ProcessGraph where
  nodes := {x, auxNode 7}
  root := .ref x
  label := fun _ => counterLabel
  root_closed := by simp [gprocRefs]
  closed := by simp [counterLabel, matchingCont, blockedCont, gprocRefs]

private abbrev allocate := fresh counterGraph [x]
private abbrev collect := tailCollectR counterGraph allowed allocate

example : collect .deadlock = some .deadlock := rfl
example : collect (.nSeq .drop (.ref x)) = collect (.ref x) := rfl
example : collect (.choice (.ref x) .deadlock) =
    some (.choice (.ref (allocate x)) .deadlock) := rfl

example : collect (.rcfgPrefix "a" .id matchingCont) =
    some (.choice (.nSeq .id (.ref x)) (.ref (allocate x))) := rfl

-- The channel agrees in both tests. The full policy pair controls the barrier.
private def unsupported : GProc := .recv "ctrl" .id .deadlock

example : collect (.rcfgPrefix "a" .drop unsupported) = some .deadlock := rfl
example : collect (.rcfgPrefix "a" .id unsupported) = none := rfl
example : collect (.ref x) = some (.ref (auxNode 8)) := rfl
example : collect (.nSeq .id unsupported) = none := rfl
example : collect (.choice unsupported .deadlock) = none := rfl
example : collect (.choice .deadlock unsupported) = none := rfl

example : collect unsupported = none := rfl
example : collect (.send "ctrl" .id .deadlock) = none := rfl
example : collect (.parallel .deadlock .deadlock) = none := rfl
example : collect (.leftMerge .deadlock .deadlock) = none := rfl
example : collect (.commMerge .deadlock .deadlock) = none := rfl
example : collect (.restrict ∅ .deadlock) = none := rfl
example : collect (.project 1 .deadlock) = none := rfl

private theorem cycleRun :
    tailRun exUnguardedGraph ∅ (tailRefsR ∅ exUnguardedGraph.root) ∅ [] = some [y, x] := by
  simp [tailRun, tailRefsR, exUnguardedGraph, exUnguardedLabel, varNode]

example : fresh exUnguardedGraph [y, x] x ≠ fresh exUnguardedGraph [y, x] y := by
  intro heq
  have hxy := fresh_inj (G := exUnguardedGraph) (L := [y, x])
    (by simp : x ∈ [y, x]) (by simp : y ∈ [y, x]) heq
  exact (by decide : x ≠ y) hxy

example : fresh exUnguardedGraph [y, x] ([y, x] : List NodeId)[1] = auxNode 2 :=
  fresh_getElem _ (tailRun_root_success _ _ _ cycleRun).1 1 (by decide)

example : maxAux counterGraph = 7 := by decide
example : allocate x ∉ counterGraph.nodes := fresh_notMem_nodes _ _ _
example : allocate y = allocate (varNode "Z") := rfl

example :
    tailCollectR exUnguardedGraph ∅ (fresh exUnguardedGraph [y, x]) exUnguardedGraph.root =
      some (.ref (fresh exUnguardedGraph [y, x] x)) :=
  (tailCollectR_root_ref_iff cycleRun (by simp)).mpr (.ref x)

example :
    tailCollectR exUnguardedGraph ∅ (fresh exUnguardedGraph [y, x]) (exUnguardedGraph.label x) =
      some (.ref (fresh exUnguardedGraph [y, x] y)) :=
  (tailCollectR_label_ref_iff cycleRun (by simp) (by simp)).mpr (.ref y)

-- Original X remains inside the packet-prefix continuation. The recursive
-- contribution uses the new auxiliary ID, and the c branch is cut locally.
private theorem counterCollection :
    collect (counterGraph.label x) =
      some (.choice (.choice (.nSeq .id (.ref x)) (.ref (auxNode 8))) .deadlock) := rfl

example (σ : CtxPkt) :
    GStep counterGraph ⟨matchingCont, [σ], []⟩ (.packet σ σ) ⟨.ref x, [], [σ]⟩ :=
  .seq_ok .id (.ref x) σ σ [] [] rfl

example (σ : CtxPkt) :
    GStep counterGraph ⟨.ref x, [], [σ]⟩ (.rcfg "c" .id) ⟨blockedCont, [], [σ]⟩ :=
  .var x _ _ _ _ _ _ (.choice_r _ _ _ _ _ _ _ _ (.rcfg "c" .id blockedCont [] [σ]))

private def reusedTail : GProc :=
  .choice (.choice matchingCont (.ref x)) .deadlock

example : tailCollectR counterGraph allowed id (counterGraph.label x) = some reusedTail := rfl

-- If X instead resolves to that collected term, no finite c-step can
-- originate at X. The recursive branch can only return to the same label.
example (H : ProcessGraph) (hLabel : H.label x = reusedTail)
    (pending handled : List CtxPkt) (dst : GConfig) :
    ¬ GStep H ⟨.ref x, pending, handled⟩ (.rcfg "c" .id) dst := by
  have noC : ∀ {src action dest}, GStep H src action dest → action = .rcfg "c" .id →
      (src.proc = .ref x ∨ src.proc = reusedTail ∨
        src.proc = .choice matchingCont (.ref x) ∨ src.proc = matchingCont ∨
        src.proc = .deadlock) → False := by
    intro src action dest hStep
    induction hStep <;> intro hAction hProc <;>
      simp [reusedTail, matchingCont] at hAction hProc
    case choice_l ih =>
      rcases hProc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih hAction (Or.inr (Or.inr (Or.inl rfl)))
      · exact ih hAction (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    case choice_r ih =>
      rcases hProc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih hAction (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      · exact ih hAction (Or.inl rfl)
    case var ih =>
      subst hProc
      exact ih hAction (Or.inr (Or.inl hLabel))
  exact fun hStep => noC hStep rfl (Or.inl rfl)

#eval allocate x
#eval [y, x].map (fresh exUnguardedGraph [y, x])
#eval (collect (.rcfgPrefix "a" .drop unsupported)).isSome
#eval (collect (.rcfgPrefix "a" .id unsupported)).isNone

#print axioms tailCollectR
#print axioms tailCollectR_choice_some_iff
#print axioms tailCollectR_choice_none_iff
#print axioms tailCollectR_rcfgPrefix_mem_some_iff
#print axioms tailCollectR_rcfgPrefix_mem_none_iff
#print axioms tailCollectR_rcfgPrefix_not_mem
#print axioms tailCollectR_image_shape
#print axioms NSeqRefSpine.mem_tailRefsR
#print axioms tailCollectR_ref_inv
#print axioms tailCollectR_ref_iff
#print axioms maxAux
#print axioms fresh
#print axioms fresh_inj
#print axioms fresh_inj_iff
#print axioms fresh_notMem_nodes
#print axioms fresh_getElem
#print axioms tailRun_root_refs_mem
#print axioms tailCollectR_root_ref_iff
#print axioms tailCollectR_label_ref_iff

end DyNetKAT.DyNetKAT.GraphTailCollectTests
