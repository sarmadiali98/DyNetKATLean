import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.EquationsAIPTests

open DyNetKAT.NetKAT

example (env : RecEnv) (p : DyNetKAT) : Derives env (.choice p p) p :=
  .ofNoAIP (.a4 p)

example (env : RecEnv) {p : DyNetKAT} (hp : WellFormed env p) : Derives env p p :=
  .aip_guarded hp hp (fun n => .refl env (.project n p))

private def loopBody : DyNetKAT := .rcfgPrefix "tick" .id (.var "X")
private def loopEnv : RecEnv := fun _ => some loopBody

private theorem loopWellFormed (p : DyNetKAT) : WellFormed loopEnv p :=
  ⟨fun _ _ => rfl, fun _ _ => ⟨loopBody, rfl, trivial⟩⟩

private theorem loopPremises (n : Nat) :
    Derives loopEnv (.project n (.var "X")) (.project n loopBody) := by
  cases n with
  | zero => exact .ofNoAIP (.trans (.projectZero _) (.symm (.projectZero _)))
  | succ n =>
    exact .ofNoAIP (.projectCongr (n + 1) (.unfold (p := loopBody) rfl))

example : Bisimilar loopEnv (.var "X") loopBody :=
  Derives.aip_guarded_sound (loopWellFormed _) (loopWellFormed _) loopPremises

-- Each projected premise is itself an AIP node, and the resulting proof
-- is used under prefix congruence, symmetry, and transitivity.
private theorem nested : Derives loopEnv (.var "X") loopBody :=
  .aip_guarded (loopWellFormed _) (loopWellFormed _) (fun n =>
    .aip_guarded (loopWellFormed _) (loopWellFormed _) (fun m =>
      .projectCongr m (loopPremises n)))

example : Bisimilar loopEnv (.send "x" .id (.var "X")) (.send "x" .id loopBody) :=
  derivability_sound (.trans
    (.prefixCongr (.send "x" .id) (.symm (.symm nested))) (.refl _ _))

private theorem wellFormed_without_refs (env : RecEnv) {p : DyNetKAT}
    (h : recursiveVars p = ∅) : WellFormed env p := by
  have unreachable (x : Var) (hx : ReachableVar env p x) : False := by
    induction hx with
    | direct hm => simp [h] at hm
    | throughDefinition _ _ _ ih => exact ih
  exact ⟨fun x hx => (unreachable x hx).elim, fun x hx => (unreachable x hx).elim⟩

-- L is an arbitrary set. The synchronization emits a reconfiguration
-- regardless of the restriction's membership test for the send or receive.
example (env : RecEnv) (L : Set CommunicationAction) :
    Bisimilar env
      (.restrict L (.commMerge (.recv "x" .id .deadlock) (.send "x" .id .deadlock)))
      (.rcfgPrefix "x" .id (.restrict L (.parallel .deadlock .deadlock))) := by
  apply Derives.aip_guarded_sound
    (wellFormed_without_refs env (by simp [recursiveVars]))
    (wellFormed_without_refs env (by simp [recursiveVars]))
  intro n
  exact .ofNoAIP (.projectCongr n (.trans (.restrictCongr L (.a12 _ _ _ _))
    (.restrictAllowed L (.visible (.rcfg "x" .id)) _ (.rcfg _ _) id)))

-- The full system retains the literal communication payload boundary.
example (env : RecEnv) (p : DyNetKAT) :
    ¬ Derives env (.send "x" (.union .id .drop) p) (.send "x" .id p) := by
  intro h
  obtain ⟨R, hR, hRelated⟩ := h.sound
  obtain ⟨_, hs, _⟩ := hR.2 _ _ hRelated [] [] (.send "x" (.union .id .drop)) p [] []
    (.cpol_send _ _ _ _ _)
  cases hs

#print axioms WellFormed.finite_targets
#print axioms WellFormed.finite_targets_from
#print axioms WellFormed.imageFiniteFrom
#print axioms approximation_induction
#print axioms Derives.aip_guarded
#print axioms Derives.aip_guarded_sound
#print axioms Derives.sound
#print axioms derivability_sound

end DyNetKAT.DyNetKAT.EquationsAIPTests
