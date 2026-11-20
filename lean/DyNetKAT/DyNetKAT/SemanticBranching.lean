import DyNetKAT.DyNetKAT.Approximation

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

variable {schema : PacketSchema}

/-- A syntactic bound on one-step targets. Restrictions and synchronization
can only remove candidates, so the bound needs no label or membership tests. -/
private def headTargets (resolve : Var → List (DyNetKAT schema)) : DyNetKAT schema → List (DyNetKAT schema)
  | .deadlock => []
  | .nSeq _ p | .recv _ _ p | .send _ _ p | .rcfgPrefix _ _ p => [p]
  | .choice p q => headTargets resolve p ++ headTargets resolve q
  | .leftMerge p q => (headTargets resolve p).map (fun p' => .parallel p' q)
  | .commMerge p q =>
      (headTargets resolve p).flatMap (fun p' => (headTargets resolve q).map (.parallel p'))
  | .parallel p q =>
      (headTargets resolve p).map (fun p' => .parallel p' q) ++
      (headTargets resolve q).map (.parallel p) ++
      (headTargets resolve p).flatMap (fun p' => (headTargets resolve q).map (.parallel p'))
  | .restrict L p => (headTargets resolve p).map (.restrict L)
  | .project 0 _ => []
  | .project (n + 1) p => (headTargets resolve p).map (.project n)
  | .var x => resolve x

/-- A reference lookup needs a bound only at positions inspected before a step. -/
private def CoversLookups (env : RecEnv schema) (resolve : Var → List (DyNetKAT schema)) : DyNetKAT schema → Prop
  | .parallel p q | .choice p q | .commMerge p q =>
      CoversLookups env resolve p ∧ CoversLookups env resolve q
  | .leftMerge p _ | .restrict _ p | .project (_ + 1) p => CoversLookups env resolve p
  | .var x => ∀ b, env.lookup x = some b → ∀ q, ProcessStep env b q → q ∈ resolve x
  | _ => True

private theorem Step.mem_headTargets {env : (RecEnv schema)} {c d : (Config schema)} {a : (Action schema)}
    (h : Step env c a d) (resolve : Var → List (DyNetKAT schema))
    (hc : CoversLookups env resolve c.proc) : d.proc ∈ headTargets resolve c.proc := by
  induction h with
  | cpol_seq_ok | cpol_recv | cpol_send | cpol_rcfg => exact List.mem_cons_self
  | cpol_choice_l _ _ _ _ _ _ _ _ _ ih => exact List.mem_append_left _ (ih hc.1)
  | cpol_choice_r _ _ _ _ _ _ _ _ _ ih => exact List.mem_append_right _ (ih hc.2)
  | cpol_left_merge _ _ _ _ _ _ _ _ _ ih => exact List.mem_map.mpr ⟨_, ih hc, rfl⟩
  | cpol_par_l _ _ _ _ _ _ _ _ _ ih =>
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, ih hc.1, rfl⟩))
  | cpol_par_r _ _ _ _ _ _ _ _ _ ih =>
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, ih hc.2, rfl⟩))
  | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂
  | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact List.mem_flatMap.mpr ⟨_, ih₁ hc.1, List.mem_map.mpr ⟨_, ih₂ hc.2, rfl⟩⟩
  | cpol_sync_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂
  | cpol_sync_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨_, ih₁ hc.1, List.mem_map.mpr ⟨_, ih₂ hc.2, rfl⟩⟩)
  | cpol_restrict _ _ _ _ _ _ _ _ _ _ ih | cpol_project _ _ _ _ _ _ _ _ _ ih =>
      exact List.mem_map.mpr ⟨_, ih hc, rfl⟩
  | cpol_var x b q a pt pt' hl hl' hb hs _ =>
      exact hc b hb q ⟨pt, hl, a, pt', hl', hs⟩

private theorem guarded_covers {env : (RecEnv schema)} {p : (DyNetKAT schema)} (h : GuardedOccurrences p)
    (resolve : Var → List (DyNetKAT schema)) : CoversLookups env resolve p := by
  induction p with
  | project n p ih => cases n <;> simp_all [CoversLookups, GuardedOccurrences]
  | _ => simp_all [CoversLookups, GuardedOccurrences]

private theorem covers_of_refs {env : (RecEnv schema)} {resolve : Var → List (DyNetKAT schema)}
    {p : (DyNetKAT schema)} (h : ∀ x ∈ recursiveVars p, CoversLookups env resolve (.var x)) :
    CoversLookups env resolve p := by
  induction p with
  | project n p ih => cases n <;> simp_all [CoversLookups, recursiveVars]
  | var x => exact h x (Finset.mem_singleton_self x)
  | _ => simp_all [CoversLookups, recursiveVars, Finset.mem_union, or_imp, forall_and]

/-- Guarded bodies contribute finitely many targets without following any
active references. A root lookup uses one such bound per referenced name. -/
theorem WellFormed.finite_targets {env : (RecEnv schema)} {p : (DyNetKAT schema)} (hw : WellFormed env p) :
    {q | ProcessStep env p q}.Finite := by
  let resolve (x : Var) := ((env.lookup x).map (headTargets (fun _ => []))).getD []
  have hc : CoversLookups env resolve p := covers_of_refs (by
    intro x hx b hb q hq
    obtain ⟨pt, hl, a, pt', hl', hs⟩ := hq
    have hg := WellFormed.reachable_guarded env p hw x b (.direct hx) hb
    simpa [resolve, hb] using hs.mem_headTargets (fun _ => []) (guarded_covers hg _))
  apply (headTargets resolve p).finite_toSet.subset
  rintro q ⟨pt, hl, a, pt', hl', hs⟩
  exact hs.mem_headTargets resolve hc

private theorem Step.direct_vars_reachable {env : (RecEnv schema)} {c d : (Config schema)} {a : (Action schema)}
    (hs : Step env c a d) {root : (DyNetKAT schema)}
    (h : ∀ x ∈ recursiveVars c.proc, ReachableVar env root x) :
    ∀ x ∈ recursiveVars d.proc, ReachableVar env root x := by
  induction hs with
  | cpol_seq_ok | cpol_recv | cpol_send | cpol_rcfg => exact h
  | cpol_restrict _ _ _ _ _ _ _ _ _ _ ih | cpol_project _ _ _ _ _ _ _ _ _ ih => exact ih h
  | cpol_var x b _ _ _ _ _ _ hb _ ih =>
    exact ih (fun _ hx => .throughDefinition (h x (Finset.mem_singleton_self x)) hb hx)
  | _ => simp_all [recursiveVars, Finset.mem_union, or_imp, forall_and]

/-- Stepping cannot introduce recursive names outside the original reachable
definition closure. -/
theorem Step.reachableVar_mono {env : (RecEnv schema)} {c d : (Config schema)} {a : (Action schema)}
    (hs : Step env c a d) {x : Var} (hx : ReachableVar env d.proc x) :
    ReachableVar env c.proc x := by
  induction hx with
  | direct h => exact hs.direct_vars_reachable (fun _ hx => .direct hx) _ h
  | throughDefinition _ hb hx ih => exact .throughDefinition ih hb hx

theorem Step.preserves_wellFormed {env : (RecEnv schema)} {c d : (Config schema)} {a : (Action schema)}
    (hs : Step env c a d) (hw : WellFormed env c.proc) : WellFormed env d.proc :=
  ⟨fun x hx => hw.1 x (hs.reachableVar_mono hx),
   fun x hx => hw.2 x (hs.reachableVar_mono hx)⟩

/-- Local finite branching on the closed, guarded source domain, independent
of the cardinality of the global derivative set or of the environment. -/
theorem WellFormed.finite_targets_from {env : RecEnv} {p : DyNetKAT} (hw : WellFormed env p)
    {q : DyNetKAT} (h : Relation.ReflTransGen (ProcessStep env) p q) :
    {r | ProcessStep env q r}.Finite := by
  have hwq : WellFormed env q := by
    induction h with
    | refl => exact hw
    | tail _ hs ih =>
      obtain ⟨pt, hl, a, pt', hl', hs⟩ := hs
      exact hs.preserves_wellFormed ih
  exact hwq.finite_targets

theorem WellFormed.imageFiniteFrom {env : RecEnv} {p : DyNetKAT} (hw : WellFormed env p) :
    ImageFiniteFrom env p := by
  intro q h pt hl a pt' hl'
  exact (hw.finite_targets_from h).subset (fun _ hs => ⟨pt, hl, a, pt', hl', hs⟩)

end DyNetKAT.DyNetKAT
