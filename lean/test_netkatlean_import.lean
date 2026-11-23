import NetKATLean

open DyNetKAT.NetKAT

private def base : CtxPkt := fun _ => .v0
private def writeOne : NetKAT := .assign1 .port .v1

example : (Packet.update base .port .v1) .port = .v1 := rfl

example : Semantics writeOne base (Packet.update base .port .v1) :=
  (assign1_sem .port .v1 _ _).mpr rfl

example : Derives (.union writeOne writeOne) writeOne := .plusIdem writeOne

example : katInterp (.union writeOne writeOne) = katInterp writeOne :=
  (Derives.plusIdem writeOne).katSound

example : Derives writeOne (normalize writeOne) := normalize_derives writeOne

#guard netkatNativeEquiv (.seq .id writeOne) writeOne
