import DyNetKAT.NetKAT.Evaluator
import DyNetKAT.NetKAT.HistoryEvaluator
import DyNetKAT.DyNetKAT.Semantics

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

/-- Membership in a supported executable result is exactly NetKAT's relational
semantics for the same input packet. -/
theorem execute_supported_iff_semantics
    (p : NetKAT) (sigma tau : CtxPkt) (outputs : Finset CtxPkt)
    (evaluates : execute p sigma = .supported outputs) :
    tau ∈ outputs ↔ Semantics p sigma tau := by
  obtain ⟨computed, hcomputed, correct⟩ := execute_correct p sigma
  have heq : outputs = computed :=
    EvalResult.supported.inj (evaluates.symm.trans hcomputed)
  rw [heq]
  exact (correct tau).symm

/-- **Singleton-history equivalence (H5A).**

    Evaluating a policy on the singleton history `History.singleton sigma` is
    semantically the same as evaluating it on the packet `sigma`: the output
    history is the singleton `History.singleton tau` exactly when the
    packet-level semantics relates `sigma` to `tau`.

    Direct consequence of the full packet/history correspondence (H3C,
    `historySemantics_iff_packetSemantics`) instantiated at the empty tails:
    the history clause additionally requires the output packet list to equal
    the input packet list, which for empty tails is `[] = []`, trivially true. -/
theorem historySemantics_singleton_iff_packetSemantics
    (p : NetKAT) (sigma tau : CtxPkt) :
    HistorySemantics p
      (History.singleton sigma)
      (History.singleton tau) ↔
      Semantics p sigma tau := by
  have key := historySemantics_iff_packetSemantics p sigma tau [] []
  constructor
  · intro hc
    exact (key.mp hc).2
  · intro hs
    exact key.mpr ⟨rfl, hs⟩

/-- Execute one NetKAT policy at the pending head of an `nSeq` configuration.
The packet histories and continuation are those of Figure 8's
`(cpol_;check)` rule: the input is removed from `pending`, and the output is
prepended to `handled`. -/
theorem execute_packet_step
    (env : RecEnv) (p : NetKAT) (continuation : DyNetKAT)
    (sigma sigma' : CtxPkt) (pendingTail handled : List CtxPkt)
    (outputs : Finset CtxPkt)
    (evaluates : execute p sigma = .supported outputs)
    (produced : sigma' ∈ outputs) :
    Step env
      ({ proc := .nSeq p continuation,
         pending := sigma :: pendingTail,
         handled := handled } : Config)
      (Action.packet sigma sigma')
      ({ proc := continuation,
         pending := pendingTail,
         handled := sigma' :: handled } : Config) := by
  apply Step.cpol_seq_ok
  exact (historySemantics_singleton_iff_packetSemantics p sigma sigma').mpr
    ((execute_supported_iff_semantics p sigma sigma' outputs evaluates).mp produced)

/-- Execute one NetKAT policy at the pending head of an `nSeq` configuration,
stated directly against the migrated history-based SOS premise: the
evaluator runs on the singleton history `History.singleton sigma`, and every
output history of a singleton input retains the (empty) input tail, so it is
itself the singleton of its head packet.  The SOS premise
`HistorySemantics p (History.singleton sigma) (History.singleton sigma')` is
established from `executeHistory_correct` plus H2 tail preservation, never
assumed. -/
theorem executeHistory_packet_step
    (env : RecEnv) (p : NetKAT) (continuation : DyNetKAT)
    (sigma : CtxPkt) (h' : History) (pendingTail handled : List CtxPkt)
    (outputs : Finset History)
    (evaluates : executeHistory p (History.singleton sigma) = .supported outputs)
    (produced : h' ∈ outputs) :
    Step env
      ({ proc := .nSeq p continuation,
         pending := sigma :: pendingTail,
         handled := handled } : Config)
      (Action.packet sigma h'.head)
      ({ proc := continuation,
         pending := pendingTail,
         handled := h'.head :: handled } : Config) := by
  apply Step.cpol_seq_ok
  obtain ⟨B, hB, corr⟩ := executeHistory_correct p (History.singleton sigma)
  have hout : outputs = B :=
    HistoryEvalResult.supported.inj (evaluates.symm.trans hB)
  rw [hout] at produced
  have hsem : HistorySemantics p (History.singleton sigma) h' := (corr h').mpr produced
  have htail : h'.tail = [] :=
    historySemantics_preserves_tail p (History.singleton sigma) h' hsem
  have heq : History.singleton h'.head = h' := by
    apply History.toList_injective
    show h'.head :: [] = h'.head :: h'.tail
    rw [htail]
  rw [heq]
  exact hsem

end DyNetKAT.DyNetKAT
