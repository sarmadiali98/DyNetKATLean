import DyNetKAT.DyNetKAT.AST
import NetKATLean.Core.Packet

open DyNetKAT.NetKAT

namespace DyNetKAT.DyNetKAT

/- Configuration `(d, H, H')` from Figure 8 of the DyNetKAT paper.
   Histories are ordered lists: the pending head is processed next, while
   the handled head is the most recently produced packet. -/
structure Config (schema : PacketSchema := ctxSchema) where
  proc : DyNetKAT schema
  pending : List schema.Packet
  handled : List schema.Packet

end DyNetKAT.DyNetKAT
