import DyNetKATLean

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

private theorem emptySupport {p : DyNetKAT} (hp : Ground p) :
    FiniteSupport RecEnv.empty p ∅ :=
  ⟨by rw [show recursiveVars p = ∅ from hp], by simp⟩

private theorem noRefs {p : DyNetKAT} (hp : Ground p) (x : Var)
    (hx : ReachableVar RecEnv.empty p x) : False := by
  have hm := reachableVars_subset_of_finiteSupport _ _ _ (emptySupport hp) x hx
  simp at hm

private theorem wellFormedGround {p : DyNetKAT} (hp : Ground p) :
    WellFormed RecEnv.empty p :=
  ⟨fun x hx => (noRefs hp x hx).elim, fun x hx => (noRefs hp x hx).elim⟩

private theorem derivesRender {p : DyNetKAT} (hp : Ground p)
    {checks : RestrictionChecks} (hc : AllRestrictionChecksCorrect (toGProc p) checks)
    {n q} (hr : renderProjection (toGraph RecEnv.empty p ∅ (emptySupport hp))
      (fun _ => allowAll) n ⟨toGProc p, checks⟩ = some q) :
    DerivesNoAIP RecEnv.empty (.project n p) q :=
  renderProjection_derives
    (toGraph_projectionSupport (emptySupport hp) (wellFormedGround hp) _
      (fun x _ hx _ => (noRefs hp x hx).elim))
    (wellFormedGround hp) (toGProc_projectionValid hc) (toGraph_corr ..) hr

private def forward : NetKAT := .assign1 .port .v1
private def packet : DyNetKAT := .nSeq forward .deadlock
private def packetTwice : DyNetKAT := .nSeq forward packet
private def packetHead : DyNetKAT := choiceOf [packet]
private def transmit : DyNetKAT := .send "sync" .id .deadlock
private def accept : DyNetKAT := .recv "sync" .id .deadlock

example : DerivesNoAIP RecEnv.empty (.project 0 packetTwice) .deadlock :=
  derivesRender (p := packetTwice) rfl (checks := allowAll) trivial rfl

example : DerivesNoAIP RecEnv.empty (.project 1 packetTwice) packetHead :=
  derivesRender (p := packetTwice) rfl (checks := allowAll) trivial rfl

example : DerivesNoAIP RecEnv.empty (.project 2 packetTwice) (choiceOf [.nSeq forward packetHead]) :=
  derivesRender (p := packetTwice) rfl (checks := allowAll) trivial rfl

example : DerivesNoAIP RecEnv.empty (.project 1 (.choice packet transmit))
    (choiceOf [packet, transmit]) :=
  derivesRender (p := .choice packet transmit) (by simp [Ground, packet, transmit, recursiveVars])
    (checks := allowAll) ⟨trivial, trivial⟩ rfl

-- Both interleavings remain available, as well as the handshake.
example : DerivesNoAIP RecEnv.empty (.project 1 (.parallel transmit accept))
    (choiceOf [transmit, accept, .rcfgPrefix "sync" .id .deadlock]) :=
  derivesRender (p := .parallel transmit accept)
    (by simp [Ground, transmit, accept, recursiveVars]) (checks := allowAll) ⟨trivial, trivial⟩ rfl

-- Blocking sends and receives leaves the synchronization in both orientations.
example : DerivesNoAIP RecEnv.empty (.project 1 (.restrict Set.univ (.parallel transmit accept)))
    handshake :=
  derivesRender (p := .restrict Set.univ (.parallel transmit accept))
    (by simp [Ground, transmit, accept, recursiveVars]) (checks := blockAll)
    ⟨by simp [blockAll], ⟨trivial, trivial⟩⟩ rfl

example : DerivesNoAIP RecEnv.empty (.project 1 (.restrict Set.univ (.parallel accept transmit)))
    handshake :=
  derivesRender (p := .restrict Set.univ (.parallel accept transmit))
    (by simp [Ground, transmit, accept, recursiveVars]) (checks := blockAll)
    ⟨by simp [blockAll], ⟨trivial, trivial⟩⟩ rfl

example : DerivesNoAIP RecEnv.empty (.project 2 (.project 1 (.commMerge accept transmit)))
    handshake :=
  derivesRender (p := .project 1 (.commMerge accept transmit))
    (by simp [Ground, transmit, accept, recursiveVars]) (checks := allowAll)
    ⟨trivial, trivial⟩ rfl

example : DerivesNoAIP RecEnv.empty (.project 1 (.leftMerge transmit accept)) (choiceOf [transmit]) :=
  derivesRender (p := .leftMerge transmit accept)
    (by simp [Ground, transmit, accept, recursiveVars]) (checks := allowAll) ⟨trivial, trivial⟩ rfl

example : ∃ q, renderProjection
    (toGraph RecEnv.empty (.parallel transmit accept) ∅ (emptySupport
      (by simp [Ground, transmit, accept, recursiveVars])))
    (fun _ => allowAll) 1
    ((CheckedResidual.mk (toGProc (.parallel transmit accept)) allowAll).restrict Set.univ (fun _ => true)) =
      some q ∧ DerivesNoAIP RecEnv.empty (.restrict Set.univ (.project 1 (.parallel transmit accept))) q :=
  renderProjection_restricted_derives (root := .parallel transmit accept)
    (emptySupport (by simp [Ground, transmit, accept, recursiveVars]))
    (wellFormedGround (by simp [Ground, transmit, accept, recursiveVars])) allowAll _
    ⟨trivial, trivial⟩ (fun x _ hx _ => (noRefs
      (by simp [Ground, transmit, accept, recursiveVars]) x hx).elim)
    Set.univ (fun _ => true) (by simp) 1

private def loopBody : DyNetKAT := .nSeq forward (.var "Loop")
private def loopEnv : RecEnv := RecEnv.empty.define "Loop" loopBody

private theorem loopSupport : FiniteSupport loopEnv (.var "Loop") {"Loop"} := by
  refine ⟨by simp [recursiveVars], ?_⟩
  intro x hx
  obtain rfl := Finset.mem_singleton.mp hx
  exact ⟨loopBody, rfl, by simp [loopBody, recursiveVars]⟩

private def loopProgram : Program false loopEnv := ⟨.var "Loop", by
  refine (paperAdmissible_iff ..).mpr ⟨trivial, ?_⟩
  intro x hx
  obtain rfl := Finset.mem_singleton.mp
    (reachableVars_subset_of_finiteSupport _ _ _ loopSupport x hx)
  exact ⟨loopBody, ⟨rfl, trivial, (typedPaperGuarded_iff_guardedOccurrences _).mpr trivial⟩, fun _ hb =>
    RecEnv.lookup_unique hb.1 (show loopEnv.lookup "Loop" = some loopBody from rfl)⟩⟩

private def compiledLoop : loopProgram.Compiled := ⟨_, loopSupport⟩

example : ∃ q, renderProjection compiledLoop.graph (fun _ => allowAll) 3
    (compiledLoop.initial allowAll).checked = some q ∧
    DerivesNoAIP loopEnv (.project 3 loopProgram.term) q := by
  have support := toGraph_projectionSupport loopSupport loopProgram.admissible.1
    (fun _ => allowAll) (fun x b hx hb => by
      obtain rfl := Finset.mem_singleton.mp
        (reachableVars_subset_of_finiteSupport _ _ _ loopSupport x hx)
      have same := RecEnv.lookup_unique hb (show loopEnv.lookup "Loop" = some loopBody from rfl)
      subst b
      trivial)
  exact compiledLoop.renderProjection_derives allowAll support (toGProc_projectionValid trivial) 3

#print axioms renderProjection_zero_derives
#print axioms WellFormed.project_exists_ground
#print axioms renderProjection_derives
#print axioms renderProjection_restricted_derives
#print axioms Program.Compiled.renderProjection_derives
#print axioms Program.Compiled.State.renderProjection_derives
#print axioms Program.Compiled.State.renderProjectionTotal_derives
#print axioms renderProjectionMemo_eq
#print axioms Program.Compiled.State.renderProjectionMemo_derives

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
