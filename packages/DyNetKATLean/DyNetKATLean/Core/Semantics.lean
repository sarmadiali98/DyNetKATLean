import DyNetKATLean.Core.Config
import DyNetKATLean.Core.Action
import DyNetKATLean.Core.RecEnv
import NetKATLean.Core.Semantics
import NetKATLean.Core.HistorySemantics

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

/-- The Figure 8 small-step relation, parameterized by recursive definitions.

    Includes `(cpolX;)` and the two `(cpol⊕)` choice rules. -/
inductive Step {schema : PacketSchema} (env : RecEnv schema) : Config schema → (Action schema) → Config schema → Prop
  | cpol_seq_ok
      (p : NetKAT schema) (q : DyNetKAT schema)
      (sigma sigma' : schema.Packet)
      (pendingTail handled : List schema.Packet)
      (evaluates : DyNetKAT.NetKAT.HistorySemantics p
        (DyNetKAT.NetKAT.History.singleton sigma)
        (DyNetKAT.NetKAT.History.singleton sigma')) :
      Step env
        (show Config schema from
          { proc := .nSeq p q, pending := sigma :: pendingTail, handled := handled })
        (show Action schema from Action.packet sigma sigma')
         (show Config schema from
           { proc := q, pending := pendingTail, handled := sigma' :: handled })

  | cpol_choice_l
      (p q p' : DyNetKAT schema) (action : Action schema)
      (pending pending' handled handled' : List schema.Packet)
      (steps : Step env
        (show Config schema from { proc := p, pending := pending, handled := handled })
        action
        (show Config schema from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config schema from { proc := .choice p q, pending := pending, handled := handled })
        action
        (show Config schema from { proc := p', pending := pending', handled := handled' })

  | cpol_choice_r
      (p q q' : DyNetKAT schema) (action : Action schema)
      (pending pending' handled handled' : List schema.Packet)
      (steps : Step env
        (show Config schema from { proc := q, pending := pending, handled := handled })
        action
        (show Config schema from { proc := q', pending := pending', handled := handled' })) :
      Step env
        (show Config schema from { proc := .choice p q, pending := pending, handled := handled })
        action
        (show Config schema from { proc := q', pending := pending', handled := handled' })

  | cpol_par_l
      (p q p' : DyNetKAT schema) (action : Action schema)
      (pending pending' handled handled' : List schema.Packet)
      (steps : Step env
        (show Config schema from { proc := p, pending := pending, handled := handled })
        action
        (show Config schema from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config schema from { proc := .parallel p q, pending := pending, handled := handled })
        action
        (show Config schema from { proc := .parallel p' q, pending := pending', handled := handled' })

  | cpol_par_r
      (p q q' : DyNetKAT schema) (action : Action schema)
      (pending pending' handled handled' : List schema.Packet)
      (steps : Step env
        (show Config schema from { proc := q, pending := pending, handled := handled })
        action
        (show Config schema from { proc := q', pending := pending', handled := handled' })) :
      Step env
         (show Config schema from { proc := .parallel p q, pending := pending, handled := handled })
         action
         (show Config schema from { proc := .parallel p q', pending := pending', handled := handled' })

  | cpol_left_merge
      (p q p' : DyNetKAT schema) (action : Action schema)
      (pending pending' handled handled' : List schema.Packet)
      (steps : Step env
        (show Config schema from { proc := p, pending := pending, handled := handled })
        action
        (show Config schema from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config schema from { proc := .leftMerge p q, pending := pending, handled := handled })
        action
        (show Config schema from
          { proc := .parallel p' q, pending := pending', handled := handled' })

  | cpol_comm_merge_recv_send
      (x : Channel) (r : NetKAT schema)
      (q s q' s' : DyNetKAT schema)
      (pending : List schema.Packet)
      (handled : List schema.Packet)
      (recv_step : Step env
        (show Config schema from { proc := q, pending := pending, handled := handled })
        (show Action schema from Action.recv x r)
        (show Config schema from { proc := q', pending := pending, handled := handled }))
      (send_step : Step env
        (show Config schema from { proc := s, pending := pending, handled := handled })
        (show Action schema from Action.send x r)
        (show Config schema from { proc := s', pending := pending, handled := handled })) :
      Step env
        (show Config schema from { proc := .commMerge q s, pending := pending, handled := handled })
        (show Action schema from Action.rcfg x r)
        (show Config schema from { proc := .parallel q' s', pending := pending, handled := handled })

  | cpol_comm_merge_send_recv
      (x : Channel) (r : NetKAT schema)
      (q s q' s' : DyNetKAT schema)
      (pending : List schema.Packet)
      (handled : List schema.Packet)
      (send_step : Step env
        (show Config schema from { proc := q, pending := pending, handled := handled })
        (show Action schema from Action.send x r)
        (show Config schema from { proc := q', pending := pending, handled := handled }))
      (recv_step : Step env
        (show Config schema from { proc := s, pending := pending, handled := handled })
        (show Action schema from Action.recv x r)
        (show Config schema from { proc := s', pending := pending, handled := handled })) :
      Step env
        (show Config schema from { proc := .commMerge q s, pending := pending, handled := handled })
        (show Action schema from Action.rcfg x r)
        (show Config schema from { proc := .parallel q' s', pending := pending, handled := handled })

  | cpol_recv
      (x : Channel) (p : NetKAT schema)
      (continuation : DyNetKAT schema)
      (pending handled : List schema.Packet) :
      Step env
        (show Config schema from
          { proc := .recv x p continuation, pending := pending, handled := handled })
        (show Action schema from Action.recv x p)
        (show Config schema from
          { proc := continuation, pending := pending, handled := handled })

  | cpol_send
      (x : Channel) (p : NetKAT schema)
      (continuation : DyNetKAT schema)
      (pending handled : List schema.Packet) :
      Step env
        (show Config schema from
          { proc := .send x p continuation, pending := pending, handled := handled })
        (show Action schema from Action.send x p)
        (show Config schema from
          { proc := continuation, pending := pending, handled := handled })

  | cpol_rcfg
      (x : Channel) (n : NetKAT schema)
      (continuation : DyNetKAT schema)
      (pending handled : List schema.Packet) :
      Step env
        (show Config schema from
          { proc := .rcfgPrefix x n continuation, pending := pending, handled := handled })
        (show Action schema from Action.rcfg x n)
        (show Config schema from
          { proc := continuation, pending := pending, handled := handled })

  | cpol_var
      (name : Var) (body body' : DyNetKAT schema) (action : Action schema)
      (pending pending' handled handled' : List schema.Packet)
      (definition : env.lookup name = some body)
      (step : Step env
        (show Config schema from { proc := body, pending := pending, handled := handled })
        action
        (show Config schema from { proc := body', pending := pending', handled := handled' })) :
      Step env
        (show Config schema from { proc := .var name, pending := pending, handled := handled })
        action
        (show Config schema from { proc := body', pending := pending', handled := handled' })

  | cpol_sync_recv_send
      (x : Channel) (r : NetKAT schema)
      (q s q' s' : DyNetKAT schema)
      (pending : List schema.Packet)
      (handled : List schema.Packet)
      (recv_step : Step env
        (show Config schema from { proc := q, pending := pending, handled := handled })
        (show Action schema from Action.recv x r)
        (show Config schema from { proc := q', pending := pending, handled := handled }))
      (send_step : Step env
        (show Config schema from { proc := s, pending := pending, handled := handled })
        (show Action schema from Action.send x r)
        (show Config schema from { proc := s', pending := pending, handled := handled })) :
      Step env
        (show Config schema from { proc := .parallel q s, pending := pending, handled := handled })
        (show Action schema from Action.rcfg x r)
        (show Config schema from { proc := .parallel q' s', pending := pending, handled := handled })

  | cpol_sync_send_recv
      (x : Channel) (r : NetKAT schema)
      (q s q' s' : DyNetKAT schema)
      (pending : List schema.Packet)
      (handled : List schema.Packet)
      (send_step : Step env
        (show Config schema from { proc := q, pending := pending, handled := handled })
        (show Action schema from Action.send x r)
        (show Config schema from { proc := q', pending := pending, handled := handled }))
      (recv_step : Step env
        (show Config schema from { proc := s, pending := pending, handled := handled })
        (show Action schema from Action.recv x r)
        (show Config schema from { proc := s', pending := pending, handled := handled })) :
      Step env
        (show Config schema from { proc := .parallel q s, pending := pending, handled := handled })
        (show Action schema from Action.rcfg x r)
        (show Config schema from { proc := .parallel q' s', pending := pending, handled := handled })

  | cpol_project
      (n : Nat)
      (p p' : DyNetKAT schema) (action : Action schema)
      (pending pending' handled handled' : List schema.Packet)
      (step : Step env
        (show Config schema from { proc := p, pending := pending, handled := handled })
        action
        (show Config schema from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config schema from
          { proc := .project (n + 1) p, pending := pending, handled := handled })
        action
        (show Config schema from
          { proc := .project n p', pending := pending', handled := handled' })

  | cpol_restrict
      (actions : Set (CommunicationAction schema))
      (p p' : DyNetKAT schema) (action : Action schema)
      (pending pending' handled handled' : List schema.Packet)
      (allowed : match action with
        | .packet _ _ => True
        | .recv x r => CommunicationAction.recv x r ∉ actions
        | .send x r => CommunicationAction.send x r ∉ actions
        | .rcfg _ _ => True)
      (step : Step env
        (show Config schema from { proc := p, pending := pending, handled := handled })
        action
        (show Config schema from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config schema from { proc := .restrict actions p, pending := pending, handled := handled })
        action
        (show Config schema from
          { proc := .restrict actions p', pending := pending', handled := handled' })

/-- Multi-step execution of the original SOS, labeled by the action list. -/
inductive Steps {schema : PacketSchema} (env : RecEnv schema) : Config schema → List (Action schema) → Config schema → Prop
  | nil (c : Config schema) : Steps env c [] c
  | cons (c c' c'' : Config schema) (a : Action schema) (acts : List (Action schema))
      (h1 : Step env c a c') (h2 : Steps env c' acts c'') :
      Steps env c (a :: acts) c''

/-- Process reachability for stateless bisimulation. Each edge may use
its own packet lists, as the bisimulation tests every possible input. -/
def ProcessStep {schema : PacketSchema} (env : RecEnv schema) (p q : DyNetKAT schema) : Prop :=
  ∃ (pt hl : List schema.Packet) (a : Action schema) (pt' hl' : List schema.Packet),
    Step env ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩

end DyNetKAT.DyNetKAT
