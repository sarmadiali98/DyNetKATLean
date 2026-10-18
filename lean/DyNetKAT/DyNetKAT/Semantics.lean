import DyNetKAT.DyNetKAT.Config
import DyNetKAT.DyNetKAT.Action
import DyNetKAT.DyNetKAT.RecEnv
import DyNetKAT.NetKAT.Semantics

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

/-- The Figure 8 small-step relation, parameterized by recursive definitions.

    Includes `(cpolX;)` and the two `(cpol⊕)` choice rules. -/
inductive Step (env : RecEnv) : Config → Action → Config → Prop
  | cpol_seq_ok
      (p : DyNetKAT.NetKAT.NetKAT) (q : DyNetKAT)
      (sigma sigma' : CtxPkt)
      (pendingTail handled : List CtxPkt)
      (evaluates : DyNetKAT.NetKAT.Semantics p sigma sigma') :
      Step env
        (show Config from
          { proc := .nSeq p q, pending := sigma :: pendingTail, handled := handled })
        (show Action from Action.packet sigma sigma')
         (show Config from
           { proc := q, pending := pendingTail, handled := sigma' :: handled })

  | cpol_choice_l
      (p q p' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (steps : Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .choice p q, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' })

  | cpol_choice_r
      (p q q' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (steps : Step env
        (show Config from { proc := q, pending := pending, handled := handled })
        action
        (show Config from { proc := q', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .choice p q, pending := pending, handled := handled })
        action
        (show Config from { proc := q', pending := pending', handled := handled' })

  | cpol_par_l
      (p q p' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (steps : Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .parallel p q, pending := pending, handled := handled })
        action
        (show Config from { proc := .parallel p' q, pending := pending', handled := handled' })

  | cpol_par_r
      (p q q' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (steps : Step env
        (show Config from { proc := q, pending := pending, handled := handled })
        action
        (show Config from { proc := q', pending := pending', handled := handled' })) :
      Step env
         (show Config from { proc := .parallel p q, pending := pending, handled := handled })
         action
         (show Config from { proc := .parallel p q', pending := pending', handled := handled' })

  | cpol_recv
      (x : Channel) (p : DyNetKAT.NetKAT.NetKAT)
      (continuation : DyNetKAT)
      (pending handled : List CtxPkt) :
      Step env
        (show Config from
          { proc := .recv x p continuation, pending := pending, handled := handled })
        (show Action from Action.recv x p)
        (show Config from
          { proc := continuation, pending := pending, handled := handled })

  | cpol_send
      (x : Channel) (p : DyNetKAT.NetKAT.NetKAT)
      (continuation : DyNetKAT)
      (pending handled : List CtxPkt) :
      Step env
        (show Config from
          { proc := .send x p continuation, pending := pending, handled := handled })
        (show Action from Action.send x p)
        (show Config from
          { proc := continuation, pending := pending, handled := handled })

  | cpol_var
      (name : Var) (body body' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (definition : env.lookup name = some body)
      (step : Step env
        (show Config from { proc := body, pending := pending, handled := handled })
        action
        (show Config from { proc := body', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .var name, pending := pending, handled := handled })
        action
        (show Config from { proc := body', pending := pending', handled := handled' })

  | cpol_sync_recv_send
      (x : Channel) (r : DyNetKAT.NetKAT.NetKAT)
      (q s q' s' : DyNetKAT)
      (pending : List CtxPkt)
      (handled : List CtxPkt)
      (recv_step : Step env
        (show Config from { proc := q, pending := pending, handled := handled })
        (show Action from Action.recv x r)
        (show Config from { proc := q', pending := pending, handled := handled }))
      (send_step : Step env
        (show Config from { proc := s, pending := pending, handled := handled })
        (show Action from Action.send x r)
        (show Config from { proc := s', pending := pending, handled := handled })) :
      Step env
        (show Config from { proc := .parallel q s, pending := pending, handled := handled })
        (show Action from Action.rcfg x r)
        (show Config from { proc := .parallel q' s', pending := pending, handled := handled })

  | cpol_sync_send_recv
      (x : Channel) (r : DyNetKAT.NetKAT.NetKAT)
      (q s q' s' : DyNetKAT)
      (pending : List CtxPkt)
      (handled : List CtxPkt)
      (send_step : Step env
        (show Config from { proc := q, pending := pending, handled := handled })
        (show Action from Action.send x r)
        (show Config from { proc := q', pending := pending, handled := handled }))
      (recv_step : Step env
        (show Config from { proc := s, pending := pending, handled := handled })
        (show Action from Action.recv x r)
        (show Config from { proc := s', pending := pending, handled := handled })) :
      Step env
        (show Config from { proc := .parallel q s, pending := pending, handled := handled })
        (show Action from Action.rcfg x r)
        (show Config from { proc := .parallel q' s', pending := pending, handled := handled })

end DyNetKAT.DyNetKAT
