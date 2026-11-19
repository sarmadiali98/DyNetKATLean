import DyNetKAT.NetKAT.Legacy
import DyNetKAT

namespace DyNetKAT.NetKAT.NormalizationTests

local instance : DecidableEq CompleteTest := (inferInstance : DecidableEq CtxPkt)
local instance : DecidableEq CompleteAssignmentValuation := (inferInstance : DecidableEq CtxPkt)

private def base : CtxPkt := fun _ => .v0
private def port1 := Packet.update base .port .v1
private def port8 := Packet.update base .port .v8
private def port9 := Packet.update base .port .v9

private def enter := NetKAT.fieldTest .port .v0
private def allow := NetKAT.seq enter (.assign1 .port .v1)
private def to8 := NetKAT.seq enter (.assign1 .port .v8)
private def to9 := NetKAT.seq (.fieldTest .port .v8) (.assign1 .port .v9)
private def path := NetKAT.union to8 to9

#guard (netkatNormalForm .drop).card == 0
#guard decide ((base, base) ∈ netkatNormalForm .id)
#guard decide ((base, port1) ∉ netkatNormalForm .id)
#guard (netkatNormalForm (.completeTest base)).card == 1
#guard decide ((port1, port1) ∉ netkatNormalForm (.completeTest base))
#guard decide ((base, port1) ∈ netkatNormalForm (.assign1 .port .v1))

-- The firewall fixture permits the port-zero to port-one forwarding step.
#guard decide ((base, port1) ∈ netkatNormalForm allow)
#guard decide ((port1, port1) ∉ netkatNormalForm allow)
#guard decide ((netkatNormalForm allow).card > 1)

#guard decide ((base, port1) ∈ netkatNormalForm (.union allow to8))
#guard decide ((base, port8) ∈ netkatNormalForm (.union allow to8))
#guard decide ((base, port9) ∈ netkatNormalForm (.seq to8 to9))

-- One step cannot reach port nine, but star can reach it in two steps.
#guard decide ((base, port9) ∉ netkatNormalForm path)
#guard decide ((base, port9) ∈ netkatNormalForm (.star path))
#guard decide ((base, base) ∈ netkatNormalForm (.star path))
#guard decide ((port9, base) ∉ netkatNormalForm (.star path))

#guard match normalize .drop with | .drop => true | _ => false
#guard netkatEquiv (normalize (.completeTest base)) (.completeTest base)

example (σ τ : CtxPkt) : Semantics (normalize (.star path)) σ τ ↔
    Semantics (.star path) σ τ :=
  normalize_correct _ _ _

example : IsPairSum (normalize (.star path)) ∧ StarFree (normalize (.star path)) :=
  ⟨normalize_pairSum _, normalize_starFree _⟩

private def branch := NormalForm.ofSummand (base, port1)

example : Derives .drop (normalize .drop) := normalize_derives_drop

example : Derives (.union branch branch) (normalize (.union branch branch)) :=
  normalize_derives_union (normalize_derives_summand _ _) (normalize_derives_summand _ _)

example : Derives (pairSum [(base, port1), (base, port1)]) (pairSum [(base, port1)]) :=
  pairSum_derives (fun _ => by simp)

-- A direct application of the certificate theorem, with no completeness premise.
example : Derives (.star enter) .id := by
  apply derives_star_boundedPolicy (n := 0)
  exact .trans (.unionCongr (.refl _) (.oneSeq _))
    (.trans (.plusComm _ _) (.baPlusOne (.pFieldEq ⟨.port, .v0⟩)))

example : Derives .id (pairSum (packetList.map fun σ => (σ, σ))) :=
  derives_id_diagonal

example : Derives enter (normalize enter) := normalize_derives_test _
example : Derives (.completeTest base) (normalize (.completeTest base)) :=
  normalize_derives_completeTest base

example : Derives (.assign1 .port .v1) (normalize (.assign1 .port .v1)) :=
  normalize_derives_assign1 _ _

example : Derives (NetKAT.seq branch (NormalForm.ofSummand (port1, port9)))
    (NormalForm.ofSummand (base, port9)) :=
  branch_seq_match _ _ _

example : Derives (NetKAT.seq branch (NormalForm.ofSummand (port8, port9))) .drop :=
  branch_seq_mismatch _ _ _ _ (by
    intro h
    have hp := congrFun h .port
    change FieldValueEnum.v1 = FieldValueEnum.v8 at hp
    cases hp)

example : Derives (.seq to8 to9) (normalize (.seq to8 to9)) :=
  normalize_derives_starFree _ ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

example : Derives allow (normalize allow) :=
  normalize_derives_seq (normalize_derives_test _) (normalize_derives_assign1 _ _)

example : Derives (.star path) (normalize (.star path)) := normalize_derives _
example : Derives (.star (.star path)) (normalize (.star (.star path))) := normalize_derives _
example : Derives (.seq (.union (.star path) allow) (.star to9))
    (normalize (.seq (.union (.star path) allow) (.star to9))) := normalize_derives _

example (p : NetKAT) : ∃ q, IsPairSum q ∧ Derives p q := exists_derives_pairSum p

#print axioms completeTest_partition
#print axioms derives_test_pairs
#print axioms derives_assign1_pairs
#print axioms branch_seq_match
#print axioms branch_seq_mismatch
#print axioms pairSum_seq
#print axioms normalize_derives_starFree
#print axioms starFree_complete
#print axioms normalize_derives
#print axioms exists_derives_pairSum

#print axioms completeTest_singleton
#print axioms completeAssignExpr_sem
#print axioms ofSummand_singleton
#print axioms normalize_correct
#print axioms normalize_history_correct
#print axioms pairSum_derives
#print axioms normalize_derives_union
#print axioms derives_star_boundedPolicy
#print axioms starFreeComplete_iff_normalize
#print axioms normalize_derives_of_starFree_complete

end DyNetKAT.NetKAT.NormalizationTests
