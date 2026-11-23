import DyNetKATLean.Core.AST
import NetKATLean.Core.Packet

open DyNetKAT.NetKAT

namespace DyNetKAT.DyNetKAT

/-- Action labels from Figure 8 of the DyNetKAT paper. -/
inductive Action (schema : PacketSchema := ctxSchema) : Type
  | packet : schema.Packet → schema.Packet → (Action schema)
  | recv : Channel → (NetKAT schema) → (Action schema)
  | send : Channel → (NetKAT schema) → (Action schema)
  | rcfg : Channel → (NetKAT schema) → (Action schema)

def Action.pendingFor {schema : PacketSchema} (a : Action schema) (tail : List schema.Packet) : List schema.Packet :=
  match a with
  | .packet input _ => input :: tail
  | _ => tail

def Action.handledAfter {schema : PacketSchema} (a : Action schema) (handled : List schema.Packet) : List schema.Packet :=
  match a with
  | .packet _ output => output :: handled
  | _ => handled

end DyNetKAT.DyNetKAT
