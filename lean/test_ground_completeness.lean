import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.GroundCompletenessTests

open DyNetKAT.NetKAT Equations

variable (env : RecEnv)

private def stop : DyNetKAT := .deadlock
private def send : DyNetKAT := .send "x" .id stop
private def recv : DyNetKAT := .recv "x" .id stop
private def rcfg : DyNetKAT := .rcfgPrefix "x" .id stop
private def testPort := NetKAT.fieldTest .port .v0
private def packet : DyNetKAT := .nSeq .id stop
private def filtered : DyNetKAT := .nSeq testPort stop

example : DerivesNoAIP env (.choice stop (.choice stop stop)) stop :=
  ground_complete (by unfold Ground; decide) (by unfold Ground; decide)
    ((a5_sound env stop).choice_right env |>.trans env (a5_sound env stop))

example : DerivesNoAIP env (.choice packet stop) packet :=
  ground_complete (by unfold Ground; decide) (by unfold Ground; decide) (a5_sound env packet)

example : DerivesNoAIP env (.choice packet filtered) (.choice filtered packet) :=
  ground_complete (by unfold Ground; decide) (by unfold Ground; decide) (a2_sound env packet filtered)

example : DerivesNoAIP env (.choice filtered filtered) filtered :=
  ground_complete (by unfold Ground; decide) (by unfold Ground; decide) (a4_sound env filtered)

private def atomicPacket (σ τ : CtxPkt) : DyNetKAT :=
  .nSeq (NormalForm.ofSummand (σ, τ)) stop

example (σ τ : CtxPkt) : DerivesNoAIP env
    (.choice (atomicPacket σ τ) stop) (atomicPacket σ τ) :=
  ground_complete rfl rfl (a5_sound env (atomicPacket σ τ))

example (σ τ : CtxPkt) : DerivesNoAIP env
    (.choice (atomicPacket σ τ) (atomicPacket τ σ))
    (.choice (atomicPacket τ σ) (atomicPacket σ τ)) :=
  ground_complete rfl rfl (a2_sound env (atomicPacket σ τ) (atomicPacket τ σ))

example (σ τ : CtxPkt) : DerivesNoAIP env
    (.choice (atomicPacket σ τ) (atomicPacket σ τ)) (atomicPacket σ τ) :=
  ground_complete rfl rfl (a4_sound env (atomicPacket σ τ))

example : DerivesNoAIP env (.choice send send) send :=
  ground_complete (by unfold Ground; decide) (by unfold Ground; decide) (a4_sound env send)

example : DerivesNoAIP env (.choice recv stop) recv :=
  ground_complete (by unfold Ground; decide) (by unfold Ground; decide) (a5_sound env recv)

example : DerivesNoAIP env (.choice rcfg rcfg) rcfg :=
  ground_complete (by unfold Ground; decide) (by unfold Ground; decide) (a4_sound env rcfg)

example : DerivesNoAIP env (.commMerge recv send) rcfg :=
  ground_complete (by unfold Ground; decide) (by unfold Ground; decide)
    ((a12_sound env "x" .id stop stop).trans env
      ((a7_sound env stop).rcfgPrefix_left env))

example : DerivesNoAIP env (.parallel send stop) send :=
  ground_complete (by unfold Ground; decide) (by unfold Ground; decide) (a7_sound env send)

example : DerivesNoAIP env (.restrict Set.univ send) stop :=
  ground_complete (by unfold Ground; decide) (by unfold Ground; decide)
    (restrict_prefix_blocked_sound env Set.univ (.send "x" .id) stop (by trivial))

example : DerivesNoAIP env (.project 1 recv) (.recv "x" .id (.project 0 stop)) :=
  ground_complete (by unfold Ground; decide) (by unfold Ground; decide) (project_prefix_sound env 0 (.recv "x" .id) stop)

-- The outer send and receive match before the distinct packet policies are compared.
private def nested (z : NetKAT) : DyNetKAT := .send "x" .id (.recv "y" .id (.nSeq z stop))

example : DerivesNoAIP env (nested (.seq testPort .id)) (nested testPort) := by
  apply ground_complete (by unfold Ground; decide) (by unfold Ground; decide)
  exact ((netkat_sound env (.seqOne _) stop).recv_left env).send_left env

example : Derives env (.nSeq (.union .id testPort) stop) (.choice packet filtered) :=
  (ground_derives_iff_bisimilar (by unfold Ground; decide) (by unfold Ground; decide)).mpr
    (a1_sound env .id testPort stop)

example : DerivesNoAIP env (.nSeq testPort stop)
    (HeadNormalForm.render (HeadNormalForm.packetHeads testPort stop)) := by
  have normalized := HeadNormalForm.packetHeads_correct env testPort stop
  apply ground_complete (by unfold Ground; decide) _ normalized.sound
  apply (HeadNormalForm.ground_render_iff _).mpr
  intro b hb
  obtain ⟨⟨α, π⟩, _, rfl⟩ := List.mem_map.mp hb
  rfl

-- The spawning root has this syntax even when X is well formed in its environment.
example : ¬ Ground (.var "X") := by unfold Ground; decide
example : ¬ Ground (.rcfgPrefix "a" .id (.parallel (.var "X") rcfg)) := by unfold Ground; decide

#print axioms Ground.guarded
#print axioms Step.ground_decreases
#print axioms Ground.exists_headNormalForm
#print axioms HeadNormalForm.ground_render_iff
#print axioms HeadNormalForm.step_iff
#print axioms AtomicPrefix.packet_realizes
#print axioms AtomicPrefix.label_eq_of_realizes
#print axioms HeadNormalForm.match_head
#print axioms HeadNormalForm.eq_nil_of_bisimilar_nil
#print axioms HeadNormalForm.absorb
#print axioms HeadNormalForm.complete_of_continuations
#print axioms HeadNormalForm.ground_complete
#print axioms ground_complete
#print axioms ground_derives_iff_bisimilar

end DyNetKAT.DyNetKAT.GroundCompletenessTests
