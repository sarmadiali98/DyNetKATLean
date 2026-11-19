import DyNetKAT.DyNetKAT.ProcessGraph
import DyNetKAT.DyNetKAT.SemanticBranching
import DyNetKAT.DyNetKAT.TypedGuardedness

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

/-- The printed grammars of Equations (1) and (6). In both, the packet
prefix has continuation `D` from Equation (1). In Equation (6), a
reference still names an extended defining body. Prefix types enforce
dup-free payloads. -/
def PaperSyntax (extended : Bool) : DyNetKAT → Prop
  | .deadlock | .var _ => True
  | .nSeq _ p => PaperSyntax false p
  | .recv _ _ p | .send _ _ p => PaperSyntax extended p
  | .choice p q | .parallel p q => PaperSyntax extended p ∧ PaperSyntax extended q
  | .rcfgPrefix _ _ p | .restrict _ p | .project _ p =>
      extended = true ∧ PaperSyntax extended p
  | .leftMerge p q | .commMerge p q => extended = true ∧ PaperSyntax extended p ∧
      PaperSyntax extended q

abbrev BaseSyntax := PaperSyntax false

theorem PaperSyntax.of_base {extended : Bool} {p : DyNetKAT}
    (base : BaseSyntax p) : PaperSyntax extended p := by
  induction p <;> simp only [PaperSyntax, Bool.false_eq_true, false_and] at *
  case nSeq => exact base
  case recv ih | send ih => exact ih base
  case choice ihp ihq | parallel ihp ihq => exact ⟨ihp base.1, ihq base.2⟩

/-- A closed program in the selected paper grammar, with guarded defining
equations. An entry such as `Host || Switch` can expose references.
`WellFormed` alone covers the repository's uniform extended AST, which
also allows extended continuations immediately below a packet prefix. -/
def PaperAdmissible (extended : Bool) (env : RecEnv) (p : DyNetKAT) : Prop :=
  WellFormed env p ∧ PaperSyntax extended p ∧
    ∀ x body, ReachableVar env p x → env.lookup x = some body → PaperSyntax extended body

abbrev BaseAdmissible := PaperAdmissible false

theorem paperAdmissible_iff (extended : Bool) (env : RecEnv) (p : DyNetKAT) :
    PaperAdmissible extended env p ↔
      PaperSyntax extended p ∧ ∀ x, ReachableVar env p x →
        ∃! body, env.lookup x = some body ∧ PaperSyntax extended body ∧
          TypedPaperGuarded body := by
  constructor
  · rintro ⟨wf, baseSyntax, bodies⟩
    refine ⟨baseSyntax, fun x hx => ?_⟩
    obtain ⟨body, lookup, guarded⟩ := wf.2 x hx
    exact ⟨body, ⟨lookup, bodies x body hx lookup,
      (typedPaperGuarded_iff_guardedOccurrences body).2 guarded⟩,
      fun _ other => RecEnv.lookup_unique other.1 lookup⟩
  · rintro ⟨baseSyntax, equations⟩
    refine ⟨⟨?_, ?_⟩, baseSyntax, ?_⟩
    · intro x hx
      obtain ⟨_, ⟨lookup, _, _⟩, _⟩ := equations x hx
      simp [lookup]
    · intro x hx
      obtain ⟨body, ⟨lookup, _, guarded⟩, _⟩ := equations x hx
      exact ⟨body, lookup, (typedPaperGuarded_iff_guardedOccurrences body).1 guarded⟩
    · intro x body hx lookup
      obtain ⟨b, ⟨hb, base, _⟩, _⟩ := equations x hx
      obtain rfl := RecEnv.lookup_unique hb lookup
      exact base

theorem baseAdmissible_iff (env : RecEnv) (p : DyNetKAT) :
    BaseAdmissible env p ↔
      BaseSyntax p ∧ ∀ x, ReachableVar env p x →
        ∃! body, env.lookup x = some body ∧ BaseSyntax body ∧ TypedPaperGuarded body :=
  paperAdmissible_iff false env p

private theorem reachableVar_of_vars_subset {env : RecEnv} {p q : DyNetKAT}
    (subset : recursiveVars p ⊆ recursiveVars q) {x : Var} :
    ReachableVar env p x → ReachableVar env q x := by
  intro h
  induction h with
  | direct occurs => exact .direct (subset occurs)
  | throughDefinition _ lookup occurs ih => exact .throughDefinition ih lookup occurs

/-- A packet prefix preserves the reachable declarations of a base-sorted continuation. -/
theorem PaperAdmissible.packetPrefix {extended : Bool} {env : RecEnv} {d : DyNetKAT}
    (admitted : PaperAdmissible extended env d) (base : BaseSyntax d)
    (p : DyNetKAT.NetKAT.NetKAT) : PaperAdmissible extended env (.nSeq p d) := by
  refine (paperAdmissible_iff ..).2 ⟨base, ?_⟩
  intro x reachable
  exact ((paperAdmissible_iff ..).1 admitted).2 x
    (reachableVar_of_vars_subset (p := .nSeq p d) (q := d) Finset.Subset.rfl reachable)

private theorem Step.preserves_paperSyntax {extended : Bool} {env : RecEnv}
    {c d : Config} {a : Action} (step : Step env c a d)
    (formed : PaperSyntax extended c.proc)
    (bodies : ∀ x body, ReachableVar env c.proc x → env.lookup x = some body →
      PaperSyntax extended body) : PaperSyntax extended d.proc := by
  induction step <;> simp only [PaperSyntax] at *
  case cpol_seq_ok => exact PaperSyntax.of_base formed
  case cpol_recv | cpol_send => exact formed
  case cpol_rcfg => exact formed.2
  case cpol_var name body _ _ _ _ _ _ lookup _ ih =>
    have nameOccurs : ReachableVar env (.var name) name := .direct (by simp)
    refine ih (bodies name body nameOccurs lookup) ?_
    exact fun x b hx => bodies x b
      (reachableVar_of_reachable_body env (.var name) name body nameOccurs lookup x hx)
  case cpol_project _ _ _ _ _ _ _ _ _ ih | cpol_restrict _ _ _ _ _ _ _ _ _ _ ih =>
    refine ⟨formed.1, ih formed.2 (fun x b hx => bodies x b (reachableVar_of_vars_subset ?_ hx))⟩
    exact Finset.Subset.rfl
  all_goals
    have left {p q other : DyNetKAT} {x : Var} (h : ReachableVar env p x)
        (eqn : recursiveVars q = recursiveVars p ∪ recursiveVars other) :
        ReachableVar env q x := reachableVar_of_vars_subset (eqn ▸ Finset.subset_union_left) h
    have right {p q other : DyNetKAT} {x : Var} (h : ReachableVar env p x)
        (eqn : recursiveVars q = recursiveVars other ∪ recursiveVars p) :
        ReachableVar env q x := reachableVar_of_vars_subset (eqn ▸ Finset.subset_union_right) h
  case cpol_choice_l _ _ _ _ _ _ _ _ _ ih =>
    exact ih formed.1 (fun x b hx => bodies x b (left hx rfl))
  case cpol_choice_r _ _ _ _ _ _ _ _ _ ih =>
    exact ih formed.2 (fun x b hx => bodies x b (right hx rfl))
  case cpol_par_l _ _ _ _ _ _ _ _ _ ih =>
    exact ⟨ih formed.1 (fun x b hx => bodies x b (left hx rfl)), formed.2⟩
  case cpol_par_r _ _ _ _ _ _ _ _ _ ih =>
    exact ⟨formed.1, ih formed.2 (fun x b hx => bodies x b (right hx rfl))⟩
  case cpol_left_merge _ _ _ _ _ _ _ _ _ ih =>
    exact ⟨ih formed.2.1 (fun x b hx => bodies x b (left hx rfl)), formed.2.2⟩
  case cpol_sync_recv_send _ _ _ _ _ _ _ _ _ _ ihp ihq |
      cpol_sync_send_recv _ _ _ _ _ _ _ _ _ _ ihp ihq =>
    exact ⟨ihp formed.1 (fun x b hx => bodies x b (left hx rfl)),
      ihq formed.2 (fun x b hx => bodies x b (right hx rfl))⟩
  case cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ihp ihq |
      cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ihp ihq =>
    exact ⟨ihp formed.2.1 (fun x b hx => bodies x b (left hx rfl)),
      ihq formed.2.2 (fun x b hx => bodies x b (right hx rfl))⟩

/-- Every residual of an admitted program belongs to the same grammar and
continues to use a closed system of guarded equations. -/
theorem Step.preserves_paperAdmissible {extended : Bool} {env : RecEnv}
    {c d : Config} {a : Action} (step : Step env c a d)
    (source : PaperAdmissible extended env c.proc) :
    PaperAdmissible extended env d.proc :=
  ⟨step.preserves_wellFormed source.1, step.preserves_paperSyntax source.2.1 source.2.2,
    fun x body hx => source.2.2 x body (step.reachableVar_mono hx)⟩

theorem Steps.preserves_wellFormed {env : RecEnv} {c d : Config} {acts : List Action}
    (steps : Steps env c acts d) (source : WellFormed env c.proc) : WellFormed env d.proc := by
  induction steps with
  | nil => exact source
  | cons _ _ _ _ _ step _ ih => exact ih (step.preserves_wellFormed source)

theorem Steps.preserves_paperAdmissible {extended : Bool} {env : RecEnv}
    {c d : Config} {acts : List Action} (steps : Steps env c acts d)
    (source : PaperAdmissible extended env c.proc) : PaperAdmissible extended env d.proc := by
  induction steps with
  | nil => exact source
  | cons _ _ _ _ _ step _ ih => exact ih (step.preserves_paperAdmissible source)

/-- Closure under the stateless reachability relation used for AIP. Each
edge may choose its own initial and final packet histories. -/
theorem PaperAdmissible.reachable {extended : Bool} {env : RecEnv} {p q : DyNetKAT}
    (source : PaperAdmissible extended env p)
    (reach : Relation.ReflTransGen (ProcessStep env) p q) :
    PaperAdmissible extended env q := by
  induction reach with
  | refl => exact source
  | tail _ edge ih =>
    obtain ⟨pt, hl, a, pt', hl', step⟩ := edge
    exact step.preserves_paperAdmissible ih

/-- Transfer admissibility to the source representative of a compiled graph
residual using the existing trace correspondence. -/
theorem GSteps.preserves_paperAdmissible {extended : Bool} {env : RecEnv}
    {G : ProcessGraph} {c d : GConfig} {acts : List Action} {p : DyNetKAT}
    (steps : GSteps G c acts d) (corr : Corr G env p c.proc)
    (source : PaperAdmissible extended env p) :
    ∃ q, PaperAdmissible extended env q ∧ Corr G env q d.proc := by
  obtain ⟨q, trace, target⟩ := gsteps_to_steps G env c d acts steps p corr
  exact ⟨q, trace.preserves_paperAdmissible source, target⟩

end DyNetKAT.DyNetKAT
