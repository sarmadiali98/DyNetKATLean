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

end DyNetKAT.DyNetKAT
