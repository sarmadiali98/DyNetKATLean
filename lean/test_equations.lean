import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.EquationTests

open DyNetKAT.NetKAT
open Equations

variable (env : RecEnv) (p q r : DyNetKAT)

example : Bisimilar env (.nSeq .drop p) .deadlock := (DerivesNoAIP.a0 p).sound
example : Bisimilar env (.nSeq (.union .id .drop) p)
    (.choice (.nSeq .id p) (.nSeq .drop p)) := (DerivesNoAIP.a1 _ _ _).sound

example : Bisimilar env (.choice p q) (.choice q p) := (DerivesNoAIP.a2 p q).sound
example : Bisimilar env (.choice (.choice p q) r) (.choice p (.choice q r)) :=
  (DerivesNoAIP.a3 p q r).sound

-- Transitivity and context congruence combine idempotence and the unit law.
example : Bisimilar env (.project 2 (.choice (.choice p p) .deadlock)) (.project 2 p) :=
  (DerivesNoAIP.projectCongr 2
    (.trans (.choiceCongr (.a4 p) (.refl _)) (.a5 p))).sound

example : Bisimilar env (.parallel p q)
    (.choice (.choice (.leftMerge p q) (.leftMerge q p)) (.commMerge p q)) :=
  (DerivesNoAIP.a8 p q).sound

example : Bisimilar env (.leftMerge (.send "x" .id p) q) (.send "x" .id (.parallel p q)) :=
  (DerivesNoAIP.a10 (.send "x" .id) p q).sound

example : Bisimilar env (.leftMerge (.choice p q) r) (.choice (.leftMerge p r) (.leftMerge q r)) :=
  (DerivesNoAIP.a11 p q r).sound

example : Bisimilar env (.commMerge (.recv "x" .id p) (.send "x" .id q))
    (.rcfgPrefix "x" .id (.parallel p q)) := (DerivesNoAIP.a12 _ _ _ _).sound

example : Bisimilar env (.commMerge (.send "x" .id p) (.recv "x" .id q))
    (.rcfgPrefix "x" .id (.parallel p q)) := (DerivesNoAIP.a12_reverse env _ _ _ _).sound

example : Bisimilar env (.commMerge (.choice p q) r) (.choice (.commMerge p r) (.commMerge q r)) :=
  (DerivesNoAIP.a13 p q r).sound

-- Appendix A distinguishes different channels and different payloads.
example : Bisimilar env (.commMerge (.recv "x" .id p) (.send "y" .id q)) .deadlock :=
  (DerivesNoAIP.a15 (.recvSend (Or.inl (by decide)))).sound

example : Bisimilar env (.commMerge (.recv "x" .id p) (.send "x" .drop q)) .deadlock :=
  (DerivesNoAIP.a15 (.recvSend (Or.inr (by intro h; cases h)))).sound

example : Bisimilar env (.restrict Set.univ (.send "x" .id p)) .deadlock :=
  (DerivesNoAIP.restrictBlocked Set.univ (.send "x" .id) p (.send _ _) (by trivial)).sound

example : Bisimilar env (.restrict ∅ (.recv "x" .id p)) (.recv "x" .id (.restrict ∅ p)) :=
  (DerivesNoAIP.restrictAllowed ∅ (.recv "x" .id) p (.recv _ _) (by simp [PrefixBlocked])).sound

-- A block-all restriction admits the reconfiguration formed by A12.
example : Bisimilar env (.restrict Set.univ (.commMerge (.recv "x" .id p) (.send "x" .id q)))
    (.rcfgPrefix "x" .id (.restrict Set.univ (.parallel p q))) :=
  (DerivesNoAIP.trans
    (.restrictCongr Set.univ (.a12 _ _ _ _))
    (.restrictAllowed Set.univ (.visible (.rcfg "x" .id)) _ (.rcfg _ _) id)).sound

example (pt hl : List CtxPkt) :
    Step env ⟨.restrict Set.univ (.commMerge (.recv "x" .id p) (.send "x" .id q)), pt, hl⟩
      (.rcfg "x" .id) ⟨.restrict Set.univ (.parallel p q), pt, hl⟩ :=
  .cpol_restrict _ _ _ _ _ _ _ _ trivial
    (.cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ (.cpol_recv _ _ _ _ _) (.cpol_send _ _ _ _ _))

example : Bisimilar env (.project 0 p) .deadlock := (DerivesNoAIP.projectZero p).sound

example (n : Nat) : Bisimilar env (.project (n + 1) (.recv "x" .id p))
    (.recv "x" .id (.project n p)) :=
  (DerivesNoAIP.projectPrefix n (.recv "x" .id) p (.recv _ _)).sound

example (α : CompleteTest) (π : CompleteAssignmentValuation) (n : Nat) :
    Bisimilar env (.project (n + 1) (.nSeq (.seq (.completeTest α) (NetKAT.completeAssignExpr π)) p))
      (.nSeq (.seq (.completeTest α) (NetKAT.completeAssignExpr π)) (.project n p)) :=
  (DerivesNoAIP.projectPrefix n _ p (.packet α π)).sound

example (n : Nat) : Bisimilar env (.project n (.choice p q)) (.choice (.project n p) (.project n q)) :=
  (DerivesNoAIP.projectChoice n p q).sound

private def loopBody : DyNetKAT := .send "x" .id (.var "X")
private def loopEnv : RecEnv := RecEnv.empty.define "X" loopBody

example : Bisimilar loopEnv (.project 1 (.var "X")) (.send "x" .id (.project 0 (.var "X"))) :=
  (DerivesNoAIP.trans
    (.projectCongr 1 (.unfold (x := "X") (p := loopBody) rfl))
    (.projectPrefix 0 (.send "x" .id) _ (.send _ _))).sound

example : Bisimilar env (.nSeq (.union .id .drop) p) (.nSeq .id p) :=
  (DerivesNoAIP.netkat p (NetKAT.Derives.plusZero .id)).sound

-- The same derivable NetKAT equation cannot replace a send payload.
example : ¬ DerivesNoAIP env (.send "x" (.union .id .drop) p) (.send "x" .id p) := by
  intro h
  obtain ⟨R, hR, hRelated⟩ := h.sound
  obtain ⟨_, hs, _⟩ := hR.2 _ _ hRelated [] [] (.send "x" (.union .id .drop)) p [] []
    (.cpol_send _ _ _ _ _)
  cases hs

#print axioms DerivesNoAIP.sound
#print axioms a1_sound
#print axioms a8_sound
#print axioms a12_sound
#print axioms a15_sound
#print axioms restrict_prefix_allowed_sound
#print axioms restrict_prefix_blocked_sound
#print axioms project_prefix_sound
#print axioms netkat_sound

end DyNetKAT.DyNetKAT.EquationTests
