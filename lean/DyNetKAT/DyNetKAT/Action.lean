import DyNetKAT.DyNetKAT.AST
import DyNetKAT.NetKAT.Packet

open DyNetKAT.NetKAT

namespace DyNetKAT.DyNetKAT

/-- Action labels from Figure 8 of the DyNetKAT paper. -/
inductive Action : Type
  | packet : CtxPkt → CtxPkt → Action
  | recv : Channel → NetKAT → Action
  | send : Channel → NetKAT → Action
  | rcfg : Channel → NetKAT → Action

def Action.pendingFor (a : Action) (tail : List CtxPkt) : List CtxPkt :=
  match a with
  | .packet input _ => input :: tail
  | _ => tail

def Action.handledAfter (a : Action) (handled : List CtxPkt) : List CtxPkt :=
  match a with
  | .packet _ output => output :: handled
  | _ => handled

end DyNetKAT.DyNetKAT
