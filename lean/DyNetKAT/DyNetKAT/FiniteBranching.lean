import DyNetKAT.DyNetKAT.Approximation
import DyNetKAT.DyNetKAT.FiniteProjection

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

/-- The canonical translation distinguishes source syntax, including names. -/
theorem toGProc_injective : Function.Injective toGProc := by
  intro p q h
  induction p generalizing q <;> cases q <;> simp [toGProc, varNode] at h
  all_goals
    first
    | cases h; rfl
    | obtain ⟨h₁, h₂, h₃⟩ := h
      congr 1 <;> solve_by_elim
    | obtain ⟨h₁, h₂⟩ := h
      congr 1 <;> solve_by_elim

/-- Source steps translate with their exact canonical targets. The general
Corr simulation permits other correspondences, so its existential target
alone does not give an injective map on source residuals. -/
theorem Step.toGraph_canonical {env : RecEnv} {root : DyNetKAT} {S : Finset Var}
    (hsup : FiniteSupport env root S) {c d : Config} {a : Action}
    (hs : Step env c a d) (hc : recursiveVars c.proc ⊆ S) :
    GStep (toGraph env root S hsup) ⟨toGProc c.proc, c.pending, c.handled⟩ a
      ⟨toGProc d.proc, d.pending, d.handled⟩ := by
  induction hs with
  | cpol_seq_ok => exact .seq_ok _ _ _ _ _ _ (by assumption)
  | cpol_recv => exact .recv _ _ _ _ _
  | cpol_send => exact .send _ _ _ _ _
  | cpol_rcfg => exact .rcfg _ _ _ _ _
  | cpol_choice_l _ _ _ _ _ _ _ _ _ ih =>
      exact .choice_l _ _ _ _ _ _ _ _ (ih (Finset.union_subset_iff.mp hc).1)
  | cpol_choice_r _ _ _ _ _ _ _ _ _ ih =>
      exact .choice_r _ _ _ _ _ _ _ _ (ih (Finset.union_subset_iff.mp hc).2)
  | cpol_par_l _ _ _ _ _ _ _ _ _ ih =>
      exact .par_l _ _ _ _ _ _ _ _ (ih (Finset.union_subset_iff.mp hc).1)
  | cpol_par_r _ _ _ _ _ _ _ _ _ ih =>
      exact .par_r _ _ _ _ _ _ _ _ (ih (Finset.union_subset_iff.mp hc).2)
  | cpol_left_merge _ _ _ _ _ _ _ _ _ ih =>
      exact .left_merge _ _ _ _ _ _ _ _ (ih (Finset.union_subset_iff.mp hc).1)
  | cpol_sync_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .sync_recv_send _ _ _ _ _ _ _ _ (ih₁ (Finset.union_subset_iff.mp hc).1)
        (ih₂ (Finset.union_subset_iff.mp hc).2)
  | cpol_sync_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .sync_send_recv _ _ _ _ _ _ _ _ (ih₁ (Finset.union_subset_iff.mp hc).1)
        (ih₂ (Finset.union_subset_iff.mp hc).2)
  | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .comm_merge_recv_send _ _ _ _ _ _ _ _ (ih₁ (Finset.union_subset_iff.mp hc).1)
        (ih₂ (Finset.union_subset_iff.mp hc).2)
  | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .comm_merge_send_recv _ _ _ _ _ _ _ _ (ih₁ (Finset.union_subset_iff.mp hc).1)
        (ih₂ (Finset.union_subset_iff.mp hc).2)
  | cpol_project _ _ _ _ _ _ _ _ _ ih =>
      exact .project _ _ _ _ _ _ _ _ (ih hc)
  | cpol_restrict _ _ _ _ _ _ _ _ allowed _ ih =>
      exact .restrict _ _ _ _ _ _ _ _ allowed (ih hc)
  | cpol_var x b q a pt pt' hl hl' hLookup _ ih =>
      have hx := hc (Finset.mem_singleton_self x)
      have hLabel := toGraph_label_varNode hsup hx
      obtain ⟨body, hBody, hSub⟩ := hsup.2 x hx
      have he := Option.some.inj (hLookup.symm.trans hBody)
      subst body
      exact .var _ _ _ _ _ _ _ (by simpa only [hLabel, hLookup, Option.getD_some] using ih hSub)

/-- One exact row bounds the set of graph targets uniformly over actions
and both packet histories. -/
theorem MovesExact.finite_graph_targets {G : ProcessGraph} {p : GProc} {row : List SymbolicMove}
    (h : MovesExact G p row) :
    {q : GProc | ∃ pt hl a pt' hl', GStep G ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩}.Finite := by
  apply (row.map Prod.snd).finite_toSet.subset
  rintro q ⟨pt, hl, a, pt', hl', hs⟩
  obtain ⟨l, hm, _⟩ := (h pt hl a q pt' hl').mp hs
  exact List.mem_map.mpr ⟨(l, q), hm, rfl⟩

/-- A canonical exact row bounds all source residuals at once. This is
stronger than finiteness for each fixed action and pair of histories. -/
theorem MovesExact.finite_source_targets {env : RecEnv} {root p : DyNetKAT} {S : Finset Var}
    {hsup : FiniteSupport env root S} {row : List SymbolicMove}
    (hc : recursiveVars p ⊆ S) (h : MovesExact (toGraph env root S hsup) (toGProc p) row) :
    {q | ProcessStep env p q}.Finite := by
  apply (h.finite_graph_targets.preimage toGProc_injective.injOn).subset
  rintro q ⟨pt, hl, a, pt', hl', hs⟩
  exact ⟨pt, hl, a, pt', hl', hs.toGraph_canonical hsup hc⟩

/-- Supported source roots have finitely many targets at every reachable
state, even when packet lists are chosen afresh at each transition. -/
theorem finite_branching_supported {env : RecEnv} {root : DyNetKAT} {S : Finset Var}
    (hsup : FiniteSupport env root S) (hw : WellFormed env root)
    (checks : RestrictionChecks) (bodyChecks : NodeId → RestrictionChecks)
    (hc : AllRestrictionChecksCorrect (toGProc root) checks)
    (hb : ∀ x b, ReachableVar env root x → env.lookup x = some b →
      AllRestrictionChecksCorrect (toGProc b) (bodyChecks (varNode x))) :
    ∀ p, Relation.ReflTransGen (ProcessStep env) root p → {q | ProcessStep env p q}.Finite := by
  let live := ProjectionLive env root
  have hG := toGraph_projectionSupport hsup hw bodyChecks hb
  have supported {p : DyNetKAT} {c : RestrictionChecks}
      (hv : (CheckedResidual.mk (toGProc p) c).Valid live) : recursiveVars p ⊆ S := by
    intro x hx
    have hm : varNode x ∈ gprocRefs (toGProc p) := by
      rw [gprocRefs_toGProc]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hv.1 (varNode x) hm
    have hxy : x = y := Sum.inl.inj he
    subst y
    exact reachableVars_subset_of_finiteSupport env root S hsup x hy
  have residual (p : DyNetKAT) (hr : Relation.ReflTransGen (ProcessStep env) root p) :
      ∃ c, (CheckedResidual.mk (toGProc p) c).Valid live := by
    induction hr with
    | refl => exact ⟨checks, toGProc_projectionValid hc⟩
    | @tail p q _ hs ih =>
      obtain ⟨c, hv⟩ := ih
      obtain ⟨row, hr⟩ := checkedMoves_exists hG hv
      obtain ⟨he, hRows⟩ := checkedMoves_spec hG hv hr
      obtain ⟨pt, hl, a, pt', hl', hs⟩ := hs
      obtain ⟨l, hm, _⟩ := (he pt hl a (toGProc q) pt' hl').mp
        (hs.toGraph_canonical hsup (supported hv))
      obtain ⟨m, hMem, hEq⟩ := List.mem_map.mp hm
      have hProc : m.2.proc = toGProc q := congrArg Prod.snd hEq
      have hv' := hRows m hMem
      exact ⟨m.2.checks, by simpa only [← hProc] using hv'⟩
  intro p hp
  obtain ⟨c, hv⟩ := residual p hp
  obtain ⟨row, hr⟩ := checkedMoves_exists hG hv
  exact (checkedMoves_spec hG hv hr).1.finite_source_targets (supported hv)

theorem imageFinite_supported {env : RecEnv} {root : DyNetKAT} {S : Finset Var}
    (hsup : FiniteSupport env root S) (hw : WellFormed env root)
    (checks : RestrictionChecks) (bodyChecks : NodeId → RestrictionChecks)
    (hc : AllRestrictionChecksCorrect (toGProc root) checks)
    (hb : ∀ x b, ReachableVar env root x → env.lookup x = some b →
      AllRestrictionChecksCorrect (toGProc b) (bodyChecks (varNode x))) :
    ImageFiniteFrom env root := by
  intro p hp pt hl a pt' hl'
  exact (finite_branching_supported hsup hw checks bodyChecks hc hb p hp).subset
    (fun _ hs => ⟨pt, hl, a, pt', hl', hs⟩)

/-- Supported-domain semantic AIP. The two roots may use different finite
supports and classifiers in the same source definition environment. -/
theorem approximation_induction_supported {env : RecEnv} {p q : DyNetKAT} {S T : Finset Var}
    (hs : FiniteSupport env p S) (ht : FiniteSupport env q T)
    (hp : WellFormed env p) (hq : WellFormed env q)
    (cp cq : RestrictionChecks) (bp bq : NodeId → RestrictionChecks)
    (hcp : AllRestrictionChecksCorrect (toGProc p) cp)
    (hcq : AllRestrictionChecksCorrect (toGProc q) cq)
    (hbp : ∀ x b, ReachableVar env p x → env.lookup x = some b →
      AllRestrictionChecksCorrect (toGProc b) (bp (varNode x)))
    (hbq : ∀ x b, ReachableVar env q x → env.lookup x = some b →
      AllRestrictionChecksCorrect (toGProc b) (bq (varNode x)))
    (h : ∀ n, Bisimilar env (.project n p) (.project n q)) : Bisimilar env p q :=
  approximation_induction (imageFinite_supported hs hp cp bp hcp hbp)
    (imageFinite_supported ht hq cq bq hcq hbq) h

end DyNetKAT.DyNetKAT
