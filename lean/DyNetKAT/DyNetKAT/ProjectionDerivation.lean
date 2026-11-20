import DyNetKAT.DyNetKAT.Program
import DyNetKAT.DyNetKAT.MemoProjection

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : NetKAT.PacketSchema} [NetKAT.DiagramLayout schema]

/-- The depth-zero rendering is the right-hand side of Figure 11's Π₀. -/
theorem renderProjection_zero_derives (env : RecEnv schema) (p : DyNetKAT schema) :
    DerivesNoAIP env (.project 0 p) .deadlock :=
  .projectZero p

private theorem project_heads_exists_ground {env : RecEnv schema} (n : Nat) (xs : HeadNormalForm schema)
    (tails : ∀ b ∈ xs, ∃ q, Ground q ∧ DerivesNoAIP env (.project n b.continuation) q) :
    ∃ q, Ground q ∧ DerivesNoAIP env (xs.project (n + 1)).render q := by
  induction xs with
  | nil => exact ⟨.deadlock, rfl, .refl _⟩
  | cons b xs ih =>
    obtain ⟨front, hFront, dFront⟩ := tails b List.mem_cons_self
    obtain ⟨rest, hRest, dRest⟩ := ih (fun c hc => tails c (List.mem_cons_of_mem _ hc))
    refine ⟨.choice (b.label.prefix front) rest, ?_, .choiceCongr (.prefixCongr _ dFront) dRest⟩
    have hPrefix : Ground (b.label.prefix front) := by
      cases label : b.label with
      | visible l => cases l <;> exact hFront
      | recv | send => exact hFront
    exact Finset.union_eq_empty.mpr ⟨hPrefix, hRest⟩

/-- Successive head normalization and Π rules eliminate recursion from a
fixed-depth projection. Only the projected continuations need induction. -/
theorem WellFormed.project_exists_ground {env : RecEnv schema} {p : DyNetKAT schema}
    (hp : WellFormed env p) (n : Nat) :
    ∃ q, Ground q ∧ DerivesNoAIP env (.project n p) q := by
  induction n generalizing p with
  | zero => exact ⟨.deadlock, rfl, renderProjection_zero_derives env p⟩
  | succ n ih =>
    obtain ⟨xs, normalize, closed⟩ := hp.exists_headNormalForm_closed
    obtain ⟨q, hq, branches⟩ := project_heads_exists_ground n xs
      (fun b hb => ih (closed b hb))
    exact ⟨q, hq, .trans (.projectCongr _ normalize)
      (.trans (HeadNormalForm.project_correct ..) branches)⟩

private theorem renderProjection_derives_of_ground {G : ProcessGraph schema}
    {bodyChecks : NodeId → RestrictionChecks schema} {n : Nat} {state : CheckedResidual schema}
    {env : RecEnv schema} {p q t : DyNetKAT schema} (hr : renderProjection G bodyChecks n state = some q)
    (ht : Ground t) (d : DerivesNoAIP env p t) (hs : Bisimilar env q p) :
    DerivesNoAIP env p q :=
  .trans d (ground_complete ht (renderProjection_closed hr)
    ((d.sound.symm env).trans env (hs.symm env)))

/-- The exact checked-move renderer derives from the source projection using
only the non-AIP equations. Ground completeness identifies the two finite
forms even when the renderer keeps packet policies grouped in single edges. -/
theorem renderProjection_derives {G : ProcessGraph schema} {bodyChecks : NodeId → RestrictionChecks schema}
    {live : NodeId → Prop} (support : ProjectionSupport G bodyChecks live)
    {env : RecEnv schema} {p q : DyNetKAT schema} {state : CheckedResidual schema} {n : Nat}
    (hp : WellFormed env p) (valid : state.Valid live) (corr : Corr G env p state.proc)
    (hr : renderProjection G bodyChecks n state = some q) :
    DerivesNoAIP env (.project n p) q := by
  obtain ⟨_, ground, derives⟩ := hp.project_exists_ground n
  exact renderProjection_derives_of_ground hr ground derives
    (renderProjection_bisimilar support valid corr hr)

/-- The existing outer-restriction renderer is also derivable when the
restriction is written outside the source projection. -/
theorem renderProjection_restricted_derives {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S) (hw : WellFormed env root)
    (checks : RestrictionChecks schema) (bodyChecks : NodeId → RestrictionChecks schema)
    (hc : AllRestrictionChecksCorrect (toGProc root) checks)
    (hb : ∀ x b, ReachableVar env root x → env.lookup x = some b →
      AllRestrictionChecksCorrect (toGProc b) (bodyChecks (varNode x)))
    (L : Set (CommunicationAction schema)) (blocked : CommunicationAction schema → Bool)
    (hL : ∀ a, blocked a = true ↔ a ∈ L) (n : Nat) :
    ∃ q, renderProjection (toGraph env root S hs) bodyChecks n
      ((CheckedResidual.mk (toGProc root) checks).restrict L blocked) = some q ∧
      DerivesNoAIP env (.restrict L (.project n root)) q := by
  obtain ⟨q, hr, hBisim⟩ := renderProjection_restricted hs hw checks bodyChecks hc hb L blocked hL n
  obtain ⟨t, ground, derives⟩ := hw.project_exists_ground n
  have hGround : Ground (.restrict L t) := ground
  exact ⟨q, hr, renderProjection_derives_of_ground hr hGround (.restrictCongr L derives) hBisim⟩

namespace Program.Compiled

variable {extended : Bool} {env : RecEnv schema} {program : Program extended env}

/-- Algebraic correctness on a reachable residual of an admitted program. -/
theorem State.renderProjection_derives {compiled : program.Compiled} (state : compiled.State)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : state.checked.Valid live) {n q}
    (hr : renderProjection compiled.graph bodyChecks n state.checked = some q) :
    DerivesNoAIP env (.project n state.source.term) q :=
  DyNetKAT.DyNetKAT.renderProjection_derives support state.source.admissible.1 valid state.corr hr

/-- Algebraic correctness at the source of an admitted program. -/
theorem renderProjection_derives (compiled : program.Compiled) (checks : RestrictionChecks schema)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : (compiled.initial checks).checked.Valid live) (n : Nat) :
    ∃ q, renderProjection compiled.graph bodyChecks n (compiled.initial checks).checked = some q ∧
      DerivesNoAIP env (.project n program.term) q := by
  obtain ⟨q, hr⟩ := renderProjection_exists support n valid
  exact ⟨q, hr, (compiled.initial checks).renderProjection_derives support valid hr⟩

/-- Algebraic correctness for the total renderer used by the bounded analysis strategy. -/
theorem State.renderProjectionTotal_derives {compiled : program.Compiled} (state : compiled.State)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : state.checked.Valid live) (n : Nat) :
    DerivesNoAIP env (.project n state.source.term)
      (renderProjectionTotal support n state.checked valid) :=
  state.renderProjection_derives support valid (renderProjectionTotal_eq_some support n _ valid)

/-- Memoized rendering erases to ordinary rendering, including for derivations. -/
theorem State.renderProjectionMemo_derives {compiled : program.Compiled} (state : compiled.State)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : state.checked.Valid live) {n q stats}
    (hr : renderProjectionMemo compiled.graph bodyChecks n state.checked = some (q, stats)) :
    DerivesNoAIP env (.project n state.source.term) q := by
  apply state.renderProjection_derives support valid
  rw [← renderProjectionMemo_eq, hr]
  rfl

end Program.Compiled
end DyNetKAT.DyNetKAT
