import DyNetKAT.DyNetKAT.NetKATBridge

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

private def ctxPktDecidableEq : DecidableEq CtxPkt := by
  intro sigma tau
  exact decidable_of_iff (∀ f ∈ NetKAT.fieldEnum, sigma f = tau f) (by
    constructor
    · intro h
      funext f
      exact h f (NetKAT.fieldEnum_complete f)
    · intro h f hf
      exact congrFun h f)

local instance : DecidableEq CtxPkt := ctxPktDecidableEq

/-- Enumerate packet-processing transitions for an `nSeq` process.

    `none` means that evaluating the policy was unsupported.  A supported
    evaluation is returned as `some`, including when its output set is empty.
    `Multiset` preserves the evaluator's executable finite enumeration without
    requiring a noncomputable ordering of a `Finset`.

    The policy is evaluated by the verified history-level evaluator
    `executeHistory` on the singleton history `History.singleton sigma` of the
    pending head; every output history's head packet produces the packet
    action and the destination configuration, exactly as before the
    history-semantics migration. -/
def packetTransitions
    (p : NetKAT) (continuation : DyNetKAT)
    (pending handled : List CtxPkt) :
    Option (Multiset (Action × Config)) :=
  match pending with
  | [] => some (∅ : Multiset (Action × Config))
  | sigma :: pendingTail =>
      match executeHistory p (History.singleton sigma) with
      | .unsupported => none
      | .supported outputs =>
          some (outputs.1.map (fun h' =>
            (Action.packet sigma h'.head,
              { proc := continuation
                pending := pendingTail
                handled := h'.head :: handled })))

example :
    (packetTransitions NetKAT.id .deadlock [examplePacket] []).map Multiset.card =
      some 1 := by
  native_decide

example :
    (packetTransitions NetKAT.drop .deadlock [examplePacket] []).map Multiset.card =
      some 0 := by
  native_decide

example :
    packetTransitions NetKAT.id .deadlock [] [] =
      some (∅ : Multiset (Action × Config)) := by
  rfl

/- Every enumerated packet transition is a valid `Step`. -/
theorem packetTransitions_sound
    (env : RecEnv)
    (p : NetKAT)
    (continuation : DyNetKAT)
    (pending handled : List CtxPkt)
    (results : Multiset (Action × Config))
    (action : Action)
    (destination : Config)
    (hEval : packetTransitions p continuation pending handled = some results)
    (hMem : (action, destination) ∈ results) :
    Step env
      { proc := .nSeq p continuation
        pending := pending
        handled := handled }
      action destination := by
  cases pending with
  | nil =>
      simp [packetTransitions] at hEval
      subst results
      simp at hMem
  | cons sigma pendingTail =>
      cases hExec : executeHistory p (History.singleton sigma) with
      | unsupported =>
          simp [packetTransitions, hExec] at hEval
      | supported outputs =>
          simp [packetTransitions, hExec] at hEval
          subst results
          rcases Multiset.mem_map.mp hMem with ⟨h', hTau, hPair⟩
          cases hPair
          exact executeHistory_packet_step env p continuation sigma h'
            pendingTail handled outputs hExec (Finset.mem_coe.mp hTau)

/- Every valid packet-processing transition is enumerated. -/
theorem packetTransitions_complete
    (env : RecEnv)
    (p : NetKAT)
    (continuation : DyNetKAT)
    (pending handled : List CtxPkt)
    (action : Action)
    (destination : Config)
    (hStep :
      Step env
        { proc := .nSeq p continuation
          pending := pending
          handled := handled }
        action destination) :
    ∃ results : Multiset (Action × Config),
      packetTransitions p continuation pending handled = some results ∧
      (action, destination) ∈ results := by
  cases hStep with
  | cpol_seq_ok p continuation sigma sigma' pendingTail handled evaluates =>
      obtain ⟨B, hExec, corr⟩ := executeHistory_correct p (History.singleton sigma)
      refine ⟨B.1.map (fun h' =>
        (Action.packet sigma h'.head,
          { proc := continuation
            pending := pendingTail
            handled := h'.head :: handled })), ?_, ?_⟩
      · simp [packetTransitions, hExec]
      · apply Multiset.mem_map.mpr
        refine ⟨History.singleton sigma', ?_, rfl⟩
        exact Finset.mem_coe.mpr ((corr (History.singleton sigma')).mp evaluates)

end DyNetKAT.DyNetKAT
