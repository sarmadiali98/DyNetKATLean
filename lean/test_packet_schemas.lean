import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.PacketSchemaTests

open DyNetKAT.NetKAT

private inductive Field
  | location | port | ssh
  deriving DecidableEq

private instance : Fintype Field :=
  ⟨{.location, .port, .ssh}, by intro f; cases f <;> simp⟩

private def Value : Field → Type
  | .location => Fin 1344
  | .port => Fin 8
  | .ssh => Bool

private instance (f : Field) : Fintype (Value f) := by
  cases f
  · exact inferInstanceAs (Fintype (Fin 1344))
  · exact inferInstanceAs (Fintype (Fin 8))
  · exact inferInstanceAs (Fintype Bool)

private instance (f : Field) : DecidableEq (Value f) := by
  cases f
  · exact inferInstanceAs (DecidableEq (Fin 1344))
  · exact inferInstanceAs (DecidableEq (Fin 8))
  · exact inferInstanceAs (DecidableEq Bool)

private abbrev large := PacketSchema.ofFields Field Value

private def atSwitch (id : Fin 1344) : large.Packet
  | .location => id
  | .port => (3 : Fin 8)
  | .ssh => true

theorem switch_identifiers_injective : Function.Injective atSwitch :=
  fun _ _ h => congrFun h Field.location

private def setLocation : NetKAT large := .assign1 Field.location (1343 : Fin 1344)

private def forward : NetKAT large :=
  .seq (NetKAT.fieldTestFor Field.location (0 : Fin 1344)) setLocation

private def arrived : large.Packet := large.model.update Field.location (1343 : Fin 1344) (atSwitch 0)

example : large.model.lookup Field.location arrived = (1343 : Fin 1344) :=
  large.model.lookup_update _ _ _

example : large.model.lookup Field.ssh arrived = true :=
  large.model.lookup_update_other _ _ _ _ (by intro h; cases h)

example : large.model.lookup Field.port arrived = (3 : Fin 8) :=
  large.model.lookup_update_other _ _ _ _ (by intro h; cases h)

private theorem forward_semantics (output : large.Packet) :
    Semantics forward (atSwitch 0) output ↔ output = arrived := by
  change (∃ mid, Semantics (NetKAT.fieldTestFor Field.location (0 : Fin 1344)) (atSwitch 0) mid ∧
    output = large.model.update Field.location (1343 : Fin 1344) mid) ↔ _
  simp [fieldTestFor_sem, atSwitch, arrived]

example : (katInterp forward).holds (atSwitch 0) arrived :=
  (katInterp_correct ..).mpr ((forward_semantics _).mpr rfl)

-- Run a policy with Kleene star on one supplied packet. The closure stabilizes
-- after reaching locations 0 and 1343, with the other fields unchanged.
#guard (execute (.star forward) (atSwitch 0)).outputs.map Finset.card == some 2
#guard (execute forward (atSwitch 1)).outputs.map Finset.card == some 0

example : Semantics (.star forward) (atSwitch 0) arrived :=
  .step ((forward_semantics _).mpr rfl) (.refl _)

private def loopEnv {schema : PacketSchema} (p : NetKAT schema) : RecEnv schema :=
  (RecEnv.emptyFor schema).define "loop" (.nSeq p (.var "loop"))

theorem loop_admitted {schema : PacketSchema} (p : NetKAT schema) :
    PaperAdmissible false (loopEnv p) (.var "loop") := by
  apply (paperAdmissible_iff ..).mpr
  refine ⟨trivial, fun x reachable => ?_⟩
  have name : x = "loop" := by
    induction reachable with
    | direct occurrence => simpa [recursiveVars] using occurrence
    | throughDefinition _ lookup occurrence ih =>
      subst_vars
      simp [loopEnv] at lookup
      subst_vars
      simpa [recursiveVars] using occurrence
  subst x
  refine ⟨.nSeq p (.var "loop"), ⟨by simp [loopEnv], trivial, ?_⟩, ?_⟩
  · exact (typedPaperGuarded_iff_guardedOccurrences _).mpr trivial
  · intro _ h
    simpa [loopEnv] using h.1.symm

private def loop {schema : PacketSchema} (p : NetKAT schema) : Program false (loopEnv p) :=
  ⟨.var "loop", loop_admitted p⟩

theorem large_packet_step (tail handled : List large.Packet) :
    Step (loopEnv forward) ⟨(loop forward).term, atSwitch 0 :: tail, handled⟩
      (.packet (atSwitch 0) arrived) ⟨(loop forward).term, tail, arrived :: handled⟩ := by
  apply Step.cpol_var "loop" (.nSeq forward (.var "loop")) _ _ _ _ _ _ (by simp [loopEnv])
  obtain ⟨outputs, computed, correct⟩ := execute_correct forward (atSwitch 0)
  exact execute_packet_step _ _ _ _ _ tail handled outputs computed
    ((correct arrived).mp ((forward_semantics _).mpr rfl))

theorem large_trace :
    (loop forward).Trace [.packet (atSwitch 0) arrived, .packet (atSwitch 0) arrived] :=
  ⟨[atSwitch 0, atSwitch 0], [], ⟨(loop forward).term, [], [arrived, arrived]⟩,
    .cons _ _ _ _ _ (large_packet_step _ _) (.cons _ _ _ _ _ (large_packet_step _ _) (.nil _))⟩

example : EndpointReachable (loop forward) none [] .id .id := by
  refine ⟨atSwitch 0, atSwitch 0, arrived, arrived, rfl, ?_, rfl⟩
  refine ⟨[.packet (atSwitch 0) arrived], ⟨[], [], rfl, by simp, rfl⟩, ?_, trivial⟩
  exact ⟨[atSwitch 0], [], _, .cons _ _ _ _ _ (large_packet_step [] []) (.nil _)⟩

private def concrete : NetKAT ctxSchema := .assign1 .port .v1

private def concreteOut : CtxPkt := Packet.update examplePacket .port .v1

example : execute concrete examplePacket = .supported {concreteOut} :=
  execute_assign1 (schema := ctxSchema) .port .v1 examplePacket

theorem concrete_packet_step :
    Step (loopEnv concrete) ⟨(loop concrete).term, [examplePacket], []⟩
      (.packet examplePacket concreteOut) ⟨(loop concrete).term, [], [concreteOut]⟩ := by
  apply Step.cpol_var "loop" (.nSeq concrete (.var "loop")) _ _ _ _ _ _ (by simp [loopEnv])
  exact execute_packet_step _ _ _ _ _ [] [] _
    (execute_assign1 (schema := ctxSchema) .port .v1 examplePacket) (Finset.mem_singleton_self _)

example : (loop concrete).Trace [.packet examplePacket concreteOut] :=
  ⟨[examplePacket], [], _, .cons _ _ _ _ _ concrete_packet_step (.nil _)⟩

example : Step RecEnv.empty
    ⟨.parallel (.send "ctrl" concrete .deadlock) (.recv "ctrl" concrete .deadlock), [examplePacket], []⟩
    (.rcfg "ctrl" concrete) ⟨.parallel .deadlock .deadlock, [examplePacket], []⟩ :=
  .cpol_sync_send_recv _ _ _ _ _ _ _ _ (.cpol_send _ _ _ _ _) (.cpol_recv _ _ _ _ _)

#print axioms switch_identifiers_injective
#print axioms execute_packet_step
#print axioms large_packet_step
#print axioms large_trace
#print axioms loop_admitted
#print axioms sourceTrace_iff_packetLists
#print axioms Program.trace_iff_reaches_residual
#print axioms historySemantics_iff_packetSemantics
#print axioms Program.historySemantics_iff_packetPrefix_bisimilar

end DyNetKAT.DyNetKAT.PacketSchemaTests
