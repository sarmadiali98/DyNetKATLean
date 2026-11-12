import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.ApproximationTests

open DyNetKAT.NetKAT

private def checks : RestrictionChecks := fun _ _ => true
private def bodyChecks : NodeId → RestrictionChecks := fun _ => checks

private theorem closedImageFinite (env : RecEnv) {p : DyNetKAT}
    (hvars : recursiveVars p = ∅) (hc : AllRestrictionChecksCorrect (toGProc p) checks) :
    ImageFiniteFrom env p := by
  have hsup : FiniteSupport env p ∅ := ⟨by simp [hvars], by simp⟩
  have noneReach x (h : ReachableVar env p x) : False := by
    simpa using reachableVars_subset_of_finiteSupport env p ∅ hsup x h
  exact imageFinite_supported hsup
    ⟨fun x h => (noneReach x h).elim, fun x h => (noneReach x h).elim⟩
    checks bodyChecks hc (fun x _ h _ => (noneReach x h).elim)

private def sync : DyNetKAT :=
  .parallel (.send "s" .id .deadlock) (.recv "s" .id .deadlock)

private def restrictedSync : DyNetKAT := .restrict Set.univ sync

example : ImageFiniteFrom RecEnv.empty (.nSeq .id .deadlock) :=
  closedImageFinite _ rfl trivial

example : ImageFiniteFrom RecEnv.empty sync :=
  closedImageFinite _ (by simp [sync, recursiveVars]) ⟨trivial, trivial⟩

example : ImageFiniteFrom RecEnv.empty restrictedSync :=
  closedImageFinite _ (by simp [restrictedSync, sync, recursiveVars])
    ⟨by simp [checks], trivial, trivial⟩

-- All finite projections of a process and a duplicate choice have exactly
-- the same transitions. This establishes the AIP premises directly.
private theorem project_duplicate (env : RecEnv) (p : DyNetKAT) (n : Nat) :
    Bisimilar env (.project n p) (.project n (.choice p p)) := by
  have same : ∀ pt hl a q pt' hl',
      Step env ⟨.project n p, pt, hl⟩ a ⟨q, pt', hl'⟩ ↔
        Step env ⟨.project n (.choice p p), pt, hl⟩ a ⟨q, pt', hl'⟩ := by
    intro pt hl a q pt' hl'
    cases n with
    | zero =>
      constructor <;> intro h <;> cases h
    | succ n =>
      constructor
      · intro h
        obtain ⟨q, rfl, hq⟩ := project_step_inv env n p pt hl a _ pt' hl' h
        exact project_step_exact_iff.mpr (.cpol_choice_l _ _ _ _ _ _ _ _ hq)
      · intro h
        obtain ⟨q, rfl, hq⟩ := project_step_inv env n (.choice p p) pt hl a _ pt' hl' h
        exact project_step_exact_iff.mpr
          ((choice_step_inv env p p pt hl a q pt' hl' hq).elim id id)
  let x := DyNetKAT.project n p
  let y := DyNetKAT.project n (.choice p p)
  let R (s t : DyNetKAT) := s = t ∨ (s = x ∧ t = y) ∨ (s = y ∧ t = x)
  refine ⟨R, ⟨?_, ?_⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · rintro _ _ (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rintro s t (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) pt hl a q pt' hl' h
    · exact ⟨q, h, Or.inl rfl⟩
    · exact ⟨q, (same ..).mp h, Or.inl rfl⟩
    · exact ⟨q, (same ..).mpr h, Or.inl rfl⟩

private theorem duplicate_closed_aip {p : DyNetKAT} (hv : recursiveVars p = ∅)
    (hc : AllRestrictionChecksCorrect (toGProc p) checks) :
    Bisimilar RecEnv.empty p (.choice p p) :=
  approximation_induction (closedImageFinite _ hv hc)
    (closedImageFinite _ (by simp [hv]) ⟨hc, hc⟩) (project_duplicate _ p)

example : Bisimilar RecEnv.empty sync (.choice sync sync) :=
  duplicate_closed_aip (by simp [sync, recursiveVars]) ⟨trivial, trivial⟩

example : Bisimilar RecEnv.empty restrictedSync (.choice restrictedSync restrictedSync) :=
  duplicate_closed_aip (by simp [restrictedSync, sync, recursiveVars])
    ⟨by simp [checks], trivial, trivial⟩

-- The two communication premises give one reconfiguration at depth one.
example (pt hl : List CtxPkt) :
    Step RecEnv.empty ⟨.project 1 restrictedSync, pt, hl⟩ (.rcfg "s" .id)
      ⟨.project 0 (.restrict Set.univ (.parallel .deadlock .deadlock)), pt, hl⟩ :=
  project_step_exact_iff.mpr
    (.cpol_restrict _ _ _ _ _ _ _ _ trivial
      (.cpol_sync_send_recv _ _ _ _ _ _ _ _ (.cpol_send _ _ _ _ _) (.cpol_recv _ _ _ _ _)))

private def loop : DyNetKAT := .var "X"
private def loopBody : DyNetKAT := .rcfgPrefix "tick" .id loop
private def loopEnv : RecEnv := RecEnv.empty.define "X" loopBody

private theorem loopImageFinite {p : DyNetKAT} (hv : recursiveVars p = {"X"})
    (hc : AllRestrictionChecksCorrect (toGProc p) checks) : ImageFiniteFrom loopEnv p := by
  have hsup : FiniteSupport loopEnv p {"X"} := by
    refine ⟨by simp [hv], ?_⟩
    intro x hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact ⟨loopBody, rfl, by simp [loopBody, loop, recursiveVars]⟩
  have name x (hx : ReachableVar loopEnv p x) : x = "X" :=
    Finset.mem_singleton.mp (reachableVars_subset_of_finiteSupport _ _ _ hsup x hx)
  have hf : WellFormed loopEnv p := by
    constructor
    · intro x hx
      rw [name x hx]
      rfl
    · intro x hx
      rw [name x hx]
      exact ⟨loopBody, rfl, trivial⟩
  apply imageFinite_supported hsup hf checks bodyChecks hc
  intro x b hx hb
  rw [name x hx, show loopEnv.lookup "X" = some loopBody from rfl] at hb
  cases hb
  trivial

example : Bisimilar loopEnv loop (.choice loop loop) :=
  approximation_induction (loopImageFinite rfl trivial)
    (loopImageFinite (by simp [loop]) ⟨trivial, trivial⟩) (project_duplicate _ _)

#print axioms finite_branching_supported
#print axioms approximation_match
#print axioms approximation_induction
#print axioms approximation_induction_supported

end DyNetKAT.DyNetKAT.ApproximationTests
