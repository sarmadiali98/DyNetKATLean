import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.SemanticLayeringTests

open DyNetKAT.NetKAT Equations

example (env : RecEnv) :
    Bisimilar env (.nSeq (.union .id .drop) .deadlock) (.nSeq .id .deadlock) :=
  (historySemantics_iff_nSeq_bisimilar env _ _ _).mp
    (NetKAT.Derives.plusZero .id).historySound

example (env : RecEnv) (a : Predicate) :
    Bisimilar env (.nSeq (.seq (.test a) (.test a)) .deadlock) (.nSeq (.test a) .deadlock) :=
  nSeq_bisimilar_of_historySemantics env _ (NetKAT.Derives.baSeqIdem a).historySound

example (env : RecEnv) :
    Bisimilar env (.nSeq (.seq (.assign1 .port .v0) (.assign1 .port .v1)) .deadlock)
      (.nSeq (.assign1 .port .v1) .deadlock) :=
  nSeq_bisimilar_of_historySemantics env _ (NetKAT.Derives.paModMod (schema := ctxSchema) .port .v0 .v1).historySound

example (env : RecEnv) (p : NetKAT) :
    Bisimilar env (.nSeq (.union .id (.seq p (.star p))) .deadlock)
      (.nSeq (.star p) .deadlock) :=
  nSeq_bisimilar_of_historySemantics env _ (NetKAT.Derives.unrollL p).historySound

example (env : RecEnv) (d : DyNetKAT) :
    ¬ Bisimilar env (.nSeq .id d) (.nSeq (.assign1 .port .v1) d) := by
  intro bisim
  let σ : CtxPkt := fun _ => .v0
  have identity : HistorySemantics .id (History.singleton σ) (History.singleton σ) :=
    (historySemantics_singleton_iff_packetSemantics .id σ σ).mpr rfl
  have assigned := (historySemantics_of_nSeq_bisimilar bisim _ _).mp identity
  have updated : σ = Packet.update σ .port .v1 :=
    (historySemantics_singleton_iff_packetSemantics ((.assign1 .port .v1 : NetKAT)) σ σ).mp assigned
  have different : FieldValueEnum.v0 = .v1 := by
    simpa [σ, Packet.update] using congrFun updated FieldName.port
  cases different

-- The same NetKAT equivalence does not permit replacing a send payload.
example (env : RecEnv) (d : DyNetKAT) :
    ¬ Bisimilar env (.send "c" (.union .id .drop) d) (.send "c" .id d) := by
  rintro ⟨R, bisim, related⟩
  obtain ⟨target, step, _⟩ := bisim.2 _ _ related [] [] _ d [] []
    (Step.cpol_send "c" (.union .id .drop) d [] [])
  have different := (send_step_inv env "c" .id d [] [] _ target [] [] step).1
  cases different

private def loop : DyNetKAT := .var "X"
private def loopBody : DyNetKAT := .send "c" .id loop
private def loopEnv : RecEnv := RecEnv.empty.define "X" loopBody

private theorem loopReachable {x : Var} (h : ReachableVar loopEnv loop x) : x = "X" := by
  induction h with
  | direct occurs => simpa [loop] using occurs
  | throughDefinition _ lookup occurs ih =>
    subst_vars
    have bodyEq := Option.some.inj ((RecEnv.lookup_define_same _ _ _).symm.trans lookup)
    subst_vars
    simpa [loopBody, loop, recursiveVars] using occurs

private def loopProgram : Program false loopEnv :=
  ⟨loop, (baseAdmissible_iff loopEnv loop).mpr ⟨trivial, fun x hx => by
    obtain rfl := loopReachable hx
    refine ⟨loopBody, ⟨by simp [loopEnv], trivial, ?_⟩, ?_⟩
    · exact (typedPaperGuarded_iff_guardedOccurrences _).mpr trivial
    · intro other proof
      exact RecEnv.lookup_unique proof.1 (by simp [loopEnv])⟩⟩

example : ¬ Ground loopProgram.term := by
  change ¬ Ground loop
  simp [Ground, loop]

example :
    Bisimilar loopEnv (loopProgram.packetPrefix trivial (.union .id .drop)).term
      (loopProgram.packetPrefix trivial .id).term :=
  (loopProgram.historySemantics_iff_packetPrefix_bisimilar trivial _ _).mp
    (NetKAT.Derives.plusZero .id).historySound

#print axioms nSeq_bisimilar_of_historySemantics
#print axioms historySemantics_of_nSeq_bisimilar
#print axioms historySemantics_iff_nSeq_bisimilar
#print axioms Program.historySemantics_iff_packetPrefix_bisimilar

end DyNetKAT.DyNetKAT.SemanticLayeringTests
