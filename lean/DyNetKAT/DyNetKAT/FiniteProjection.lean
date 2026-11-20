import DyNetKAT.DyNetKAT.GraphMoves
import DyNetKAT.DyNetKAT.GraphRestriction

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

def MoveLabel.prefix {schema : PacketSchema} (l : MoveLabel schema)
    (p : DyNetKAT schema) : DyNetKAT schema :=
  match l with
  | .visible (.packet N) => .nSeq N p
  | .visible (.rcfg x N) => .rcfgPrefix x N p
  | .recv x N => .recv x N p
  | .send x N => .send x N p

theorem MoveLabel.prefix_step_iff {schema : PacketSchema} (env : RecEnv schema)
    (l : MoveLabel schema) (p q : DyNetKAT schema)
    (pt hl : List schema.Packet) (a : Action schema) (pt' hl' : List schema.Packet) :
    Step env ⟨l.prefix p, pt, hl⟩ a ⟨q, pt', hl'⟩ ↔
      q = p ∧ MoveLabel.Realizes l pt hl a pt' hl' := by
  constructor
  · intro h
    cases l with
    | visible l =>
      cases l with
      | packet => cases h; exact ⟨rfl, .packet (by assumption)⟩
      | rcfg => cases h; exact ⟨rfl, .rcfg⟩
    | recv => cases h; exact ⟨rfl, .recv⟩
    | send => cases h; exact ⟨rfl, .send⟩
  · rintro ⟨rfl, h⟩
    cases h with
    | packet h => exact .cpol_seq_ok _ _ _ _ _ _ h
    | rcfg => exact .cpol_rcfg _ _ _ _ _
    | recv => exact .cpol_recv _ _ _ _ _
    | send => exact .cpol_send _ _ _ _ _

theorem choiceOf_step_iff {schema : PacketSchema} (env : RecEnv schema)
    (branches : List (DyNetKAT schema)) (pt hl : List schema.Packet) (a : Action schema)
    (q : DyNetKAT schema) (pt' hl' : List schema.Packet) :
    Step env ⟨choiceOf branches, pt, hl⟩ a ⟨q, pt', hl'⟩ ↔
      ∃ b ∈ branches, Step env ⟨b, pt, hl⟩ a ⟨q, pt', hl'⟩ := by
  induction branches with
  | nil =>
    simp only [List.not_mem_nil, false_and, exists_false, iff_false]
    intro h
    cases h
  | cons b bs ih =>
    constructor
    · intro h
      rcases choice_step_inv env b (choiceOf bs) pt hl a q pt' hl' h with h | h
      · exact ⟨b, List.mem_cons_self, h⟩
      · obtain ⟨d, hd, hs⟩ := ih.mp h
        exact ⟨d, List.mem_cons_of_mem _ hd, hs⟩
    · rintro ⟨d, hd, hs⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact .cpol_choice_l _ _ _ _ _ _ _ _ hs
      · exact .cpol_choice_r _ _ _ _ _ _ _ _ (ih.mpr ⟨d, hd, hs⟩)

/-- Render a finite prefix-and-choice term. Only an actual row edge causes
a recursive call at the next smaller depth. -/
def renderProjection (G : ProcessGraph) (bodyChecks : NodeId → RestrictionChecks) :
    Nat → CheckedResidual → Option DyNetKAT
  | 0, _ => some .deadlock
  | n + 1, p => do
      let row ← checkedMoves G bodyChecks p
      let branches ← row.mapM fun m =>
        (renderProjection G bodyChecks n m.2).map m.1.prefix
      return choiceOf branches

private theorem mapM_exists {α β : Type} {f : α → Option β} {xs : List α}
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys⟩ := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

private theorem mapM_members {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) (y : β) :
    y ∈ ys ↔ ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => cases h; simp
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨zs, hzs, he⟩ := Option.bind_eq_some_iff.mp h
    cases he
    simp only [List.mem_cons, ih hzs, hz, Option.some.injEq]
    constructor
    · rintro (rfl | ⟨w, hw, hf⟩)
      · exact ⟨x, Or.inl rfl, hz⟩
      · exact ⟨w, Or.inr hw, hf⟩
    · rintro ⟨w, rfl | hw, hf⟩
      · exact Or.inl (by simpa [hz] using hf.symm)
      · exact Or.inr ⟨w, hw, hf⟩

theorem renderProjection_exists {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {live : NodeId → Prop} (hG : ProjectionSupport G bodyChecks live)
    (n : Nat) {p : CheckedResidual} (hp : p.Valid live) :
    ∃ q, renderProjection G bodyChecks n p = some q := by
  induction n generalizing p with
  | zero => exact ⟨.deadlock, rfl⟩
  | succ n ih =>
    obtain ⟨row, hr⟩ := checkedMoves_exists hG hp
    have hv := (checkedMoves_spec hG hp hr).2
    obtain ⟨branches, hb⟩ := mapM_exists (xs := row)
      (f := fun m => (renderProjection G bodyChecks n m.2).map m.1.prefix)
      (fun m hm => by
        obtain ⟨r, he⟩ := ih (hv m hm)
        exact ⟨m.1.prefix r, by simp [he]⟩)
    exact ⟨choiceOf branches, by simp [renderProjection, hr, hb]⟩

private theorem choiceOf_closed (branches : List DyNetKAT)
    (h : ∀ b ∈ branches, recursiveVars b = ∅) : recursiveVars (choiceOf branches) = ∅ := by
  induction branches with
  | nil => rfl
  | cons b bs ih =>
    rw [choiceOf, recursiveVars, h b List.mem_cons_self,
      ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    simp

/-- The rendered tree is independent of the recursive definition table. -/
theorem renderProjection_closed {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {n : Nat} {p : CheckedResidual} {q : DyNetKAT}
    (h : renderProjection G bodyChecks n p = some q) : recursiveVars q = ∅ := by
  induction n generalizing p q with
  | zero => cases h; rfl
  | succ n ih =>
    obtain ⟨row, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨branches, hb, he⟩ := Option.bind_eq_some_iff.mp h
    cases he
    have hClosed : ∀ b ∈ branches, recursiveVars b = ∅ := by
      intro b hm
      obtain ⟨m, _, hMap⟩ := (mapM_members hb b).mp hm
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some'.mp hMap
      have hc := ih hq
      obtain ⟨l, _⟩ := m
      cases l with
      | visible label => cases label <;> exact hc
      | _ => exact hc
    exact choiceOf_closed branches hClosed

private theorem rendered_step_iff {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {row : List CheckedMove} {branches : List DyNetKAT} {n : Nat}
    (hb : row.mapM (fun m => (renderProjection G bodyChecks n m.2).map m.1.prefix) =
      some branches) (env : RecEnv)
    (pt hl : List CtxPkt) (a : Action) (q : DyNetKAT) (pt' hl' : List CtxPkt) :
    Step env ⟨choiceOf branches, pt, hl⟩ a ⟨q, pt', hl'⟩ ↔
      ∃ m ∈ row, renderProjection G bodyChecks n m.2 = some q ∧
        MoveLabel.Realizes m.1 pt hl a pt' hl' := by
  rw [choiceOf_step_iff]
  constructor
  · rintro ⟨b, hMem, hs⟩
    obtain ⟨m, hm, hMap⟩ := (mapM_members hb b).mp hMem
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some'.mp hMap
    obtain ⟨rfl, ha⟩ := (MoveLabel.prefix_step_iff ..).mp hs
    exact ⟨m, hm, hr, ha⟩
  · rintro ⟨m, hm, hr, ha⟩
    exact ⟨m.1.prefix q, (mapM_members hb _).mpr ⟨m, hm, by simp [hr]⟩,
      (MoveLabel.prefix_step_iff ..).mpr ⟨rfl, ha⟩⟩

/-- A successful rendering is strongly bisimilar to the source projection. -/
theorem renderProjection_bisimilar {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {live : NodeId → Prop} (hG : ProjectionSupport G bodyChecks live)
    {env : RecEnv} {p q : DyNetKAT} {state : CheckedResidual} {n : Nat}
    (hv : state.Valid live) (hc : Corr G env p state.proc)
    (hr : renderProjection G bodyChecks n state = some q) :
    Bisimilar env q (.project n p) := by
  let R (q s : DyNetKAT) : Prop := ∃ (n : Nat) (state : CheckedResidual) (p : DyNetKAT),
    state.Valid live ∧ Corr G env p state.proc ∧
    renderProjection G bodyChecks n state = some q ∧ s = .project n p
  have forward : ∀ q s, R q s → ∀ pt hl a q' pt' hl',
      Step env ⟨q, pt, hl⟩ a ⟨q', pt', hl'⟩ →
      ∃ s', Step env ⟨s, pt, hl⟩ a ⟨s', pt', hl'⟩ ∧ R q' s' := by
    rintro q s ⟨d, t, p, hValid, hCorr, hRender, rfl⟩ pt hl a q' pt' hl' hs
    cases d with
    | zero => cases hRender; cases hs
    | succ d =>
      obtain ⟨row, hRow, hRender⟩ := Option.bind_eq_some_iff.mp hRender
      obtain ⟨branches, hBranches, he⟩ := Option.bind_eq_some_iff.mp hRender
      cases he
      obtain ⟨m, hm, hNext, hReal⟩ := (rendered_step_iff hBranches ..).mp hs
      obtain ⟨hExact, hValidRow⟩ := checkedMoves_spec hG hValid hRow
      obtain ⟨p', hp', hc'⟩ := (hExact.source_steps hCorr pt hl a pt' hl').1
        m.1 m.2.proc (List.mem_map.mpr ⟨m, hm, rfl⟩) hReal
      exact ⟨.project d p', .cpol_project _ _ _ _ _ _ _ _ hp',
        d, m.2, p', hValidRow m hm, hc', hNext, rfl⟩
  have backward : ∀ q s, R q s → ∀ pt hl a s' pt' hl',
      Step env ⟨s, pt, hl⟩ a ⟨s', pt', hl'⟩ →
      ∃ q', Step env ⟨q, pt, hl⟩ a ⟨q', pt', hl'⟩ ∧ R q' s' := by
    rintro q s ⟨d, t, p, hValid, hCorr, hRender, rfl⟩ pt hl a s' pt' hl' hs
    cases d with
    | zero => cases hs
    | succ d =>
      obtain ⟨p', rfl, hp'⟩ := project_step_inv env d p pt hl a s' pt' hl' hs
      obtain ⟨row, hRow, hRender⟩ := Option.bind_eq_some_iff.mp hRender
      obtain ⟨branches, hBranches, he⟩ := Option.bind_eq_some_iff.mp hRender
      cases he
      obtain ⟨hExact, hValidRow⟩ := checkedMoves_spec hG hValid hRow
      obtain ⟨l, u, hm, hReal, hc'⟩ := (hExact.source_steps hCorr pt hl a pt' hl').2 p' hp'
      obtain ⟨m, hMem, he⟩ := List.mem_map.mp hm
      have hLabel : m.1 = l := congrArg Prod.fst he
      have hProc : m.2.proc = u := congrArg Prod.snd he
      obtain ⟨q', hNext⟩ := renderProjection_exists hG d (hValidRow m hMem)
      exact ⟨q', (rendered_step_iff hBranches ..).mpr
        ⟨m, hMem, hNext, hLabel ▸ hReal⟩,
        d, m.2, p', hValidRow m hMem, hProc ▸ hc', hNext, rfl⟩
  refine ⟨fun q s => R q s ∨ R s q, ⟨fun _ _ h => h.symm, ?_⟩,
    Or.inl ⟨n, state, p, hv, hc, hr, rfl⟩⟩
  intro q s h pt hl a q' pt' hl' hs
  rcases h with h | h
  · obtain ⟨s', hs', hR⟩ := forward q s h pt hl a q' pt' hl' hs
    exact ⟨s', hs', Or.inl hR⟩
  · obtain ⟨s', hs', hR⟩ := backward s q h pt hl a q' pt' hl' hs
    exact ⟨s', hs', Or.inr hR⟩

/-- Every finite graph execution can carry classifier data to its endpoint. -/
theorem GSteps.checkedResidual {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {live : NodeId → Prop} (hG : ProjectionSupport G bodyChecks live)
    {c d : GConfig} {actions : List Action} (h : GSteps G c actions d) :
    ∀ p : CheckedResidual, p.proc = c.proc → p.Valid live →
      ∃ q : CheckedResidual, q.proc = d.proc ∧ q.Valid live := by
  induction h with
  | nil => exact fun p hp hv => ⟨p, hp, hv⟩
  | cons c c' d a actions hs _ ih =>
    rintro ⟨p, checks⟩ hp hv
    cases c with
    | mk src pt hl =>
      change p = src at hp
      subst p
      obtain ⟨row, hr⟩ := checkedMoves_exists hG hv
      obtain ⟨he, hValid⟩ := checkedMoves_spec hG hv hr
      cases c' with
      | mk dst pt' hl' =>
        obtain ⟨l, hm, _⟩ := (he pt hl a dst pt' hl').mp hs
        obtain ⟨m, hMem, hEq⟩ := List.mem_map.mp hm
        exact ih m.2 (congrArg Prod.snd hEq) (hValid m hMem)

/-- Source executions lift to valid classifier-carrying residuals via Corr. -/
theorem Steps.checkedResidual {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {live : NodeId → Prop} (hG : ProjectionSupport G bodyChecks live)
    {env : RecEnv} {c d : Config} {actions : List Action} (h : Steps env c actions d)
    {p : CheckedResidual} (hc : Corr G env c.proc p.proc) (hv : p.Valid live) :
    ∃ q : CheckedResidual, Corr G env d.proc q.proc ∧ q.Valid live := by
  obtain ⟨gp, hg, hCorr⟩ := steps_to_gsteps G env c d actions h p.proc hc
  obtain ⟨q, hEq, hValid⟩ := hg.checkedResidual hG p rfl hv
  exact ⟨q, hEq ▸ hCorr, hValid⟩

/-- The reachable-name invariant allows a supplied support to contain extra
definitions that need neither guard proofs nor classifier proofs. -/
def ProjectionLive (env : RecEnv) (root : DyNetKAT) (i : NodeId) : Prop :=
  ∃ x, ReachableVar env root x ∧ i = varNode x

theorem toGraph_projectionSupport {env : RecEnv} {root : DyNetKAT} {S : Finset Var}
    (hs : FiniteSupport env root S) (hw : WellFormed env root)
    (bodyChecks : NodeId → RestrictionChecks)
    (hb : ∀ x b, ReachableVar env root x → env.lookup x = some b →
      AllRestrictionChecksCorrect (toGProc b) (bodyChecks (varNode x))) :
    ProjectionSupport (toGraph env root S hs) bodyChecks (ProjectionLive env root) := by
  have label (x : Var) (hx : ReachableVar env root x) :
      ∃ b, env.lookup x = some b ∧ (toGraph env root S hs).label (varNode x) = toGProc b := by
    obtain ⟨b, he⟩ := WellFormed.reachable_definition env root hw x hx
    refine ⟨b, he, ?_⟩
    rw [toGraph_label_varNode hs (reachableVars_subset_of_finiteSupport env root S hs x hx), he]
    rfl
  constructor
  · rintro i ⟨x, hx, rfl⟩ j hj
    obtain ⟨b, he, hLabel⟩ := label x hx
    rw [hLabel, gprocRefs_toGProc, Finset.mem_image] at hj
    obtain ⟨y, hy, rfl⟩ := hj
    exact ⟨y, .throughDefinition hx he hy, rfl⟩
  · rintro i ⟨x, hx, rfl⟩
    obtain ⟨b, he, hLabel⟩ := label x hx
    rw [hLabel]
    exact ⟨guarded_body_moveAdmissible (WellFormed.reachable_guarded env root hw x b hx he),
      hb x b hx he⟩

theorem toGProc_projectionValid {env : RecEnv} {root : DyNetKAT} {checks : RestrictionChecks}
    (h : AllRestrictionChecksCorrect (toGProc root) checks) :
    (CheckedResidual.mk (toGProc root) checks).Valid (ProjectionLive env root) := by
  refine ⟨?_, h⟩
  intro i hi
  rw [gprocRefs_toGProc, Finset.mem_image] at hi
  obtain ⟨x, hx, rfl⟩ := hi
  exact ⟨x, .direct hx, rfl⟩

/-- The proof of success is erased. The term is selected from the executable
Option result, using no choice principle. -/
def renderProjectionTotal {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {live : NodeId → Prop} (hG : ProjectionSupport G bodyChecks live)
    (n : Nat) (p : CheckedResidual) (hp : p.Valid live) : DyNetKAT :=
  (renderProjection G bodyChecks n p).get (by
    obtain ⟨q, hq⟩ := renderProjection_exists hG n hp
    simp [hq])

theorem renderProjectionTotal_eq_some {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {live : NodeId → Prop} (hG : ProjectionSupport G bodyChecks live)
    (n : Nat) (p : CheckedResidual) (hp : p.Valid live) :
    renderProjection G bodyChecks n p = some (renderProjectionTotal hG n p hp) :=
  (Option.some_get _).symm

theorem renderProjection_source {env : RecEnv} {root : DyNetKAT} {S : Finset Var}
    (hs : FiniteSupport env root S) (hw : WellFormed env root)
    (checks : RestrictionChecks) (bodyChecks : NodeId → RestrictionChecks)
    (hc : AllRestrictionChecksCorrect (toGProc root) checks)
    (hb : ∀ x b, ReachableVar env root x → env.lookup x = some b →
      AllRestrictionChecksCorrect (toGProc b) (bodyChecks (varNode x))) (n : Nat) :
    ∃ q, renderProjection (toGraph env root S hs) bodyChecks n ⟨toGProc root, checks⟩ = some q ∧
      Bisimilar env q (.project n root) := by
  have hG := toGraph_projectionSupport hs hw bodyChecks hb
  have hv := toGProc_projectionValid (env := env) hc
  obtain ⟨q, hq⟩ := renderProjection_exists hG n hv
  exact ⟨q, hq, renderProjection_bisimilar hG hv (toGraph_corr env root S hs) hq⟩

/-- Render with an extra outer restriction, using the same compiled graph. -/
theorem renderProjection_restricted {env : RecEnv} {root : DyNetKAT} {S : Finset Var}
    (hs : FiniteSupport env root S) (hw : WellFormed env root)
    (checks : RestrictionChecks) (bodyChecks : NodeId → RestrictionChecks)
    (hc : AllRestrictionChecksCorrect (toGProc root) checks)
    (hb : ∀ x b, ReachableVar env root x → env.lookup x = some b →
      AllRestrictionChecksCorrect (toGProc b) (bodyChecks (varNode x)))
    (L : Set CommunicationAction) (blocked : CommunicationAction → Bool)
    (hL : ∀ a, blocked a = true ↔ a ∈ L) (n : Nat) :
    ∃ q, renderProjection (toGraph env root S hs) bodyChecks n
      ((CheckedResidual.mk (toGProc root) checks).restrict L blocked) = some q ∧
      Bisimilar env q (.restrict L (.project n root)) := by
  have hG := toGraph_projectionSupport hs hw bodyChecks hb
  have hv := toGProc_projectionValid (env := env) hc
  have hRestricted : ((CheckedResidual.mk (toGProc root) checks).restrict L blocked).Valid
      (ProjectionLive env root) := ⟨hv.1, hL, hc⟩
  obtain ⟨q, hq⟩ := renderProjection_exists hG n hRestricted
  have hB := renderProjection_bisimilar hG hRestricted
    (corr_restrict_intro (L := L) (toGraph_corr env root S hs)) hq
  exact ⟨q, hq, hB.trans env (Bisimilar.symm env (restrict_project_commute env L root n))⟩

theorem renderProjection_preprocessable {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {n : Nat} {state : CheckedResidual} {q : DyNetKAT}
    (render : renderProjection G bodyChecks n state = some q) :
    (blockCommunication (toGProc q)).isSome := by
  induction n generalizing state q with
  | zero => cases render; rfl
  | succ n ih =>
      obtain ⟨row, _, render⟩ := Option.bind_eq_some_iff.mp render
      obtain ⟨branches, hb, eq⟩ := Option.bind_eq_some_iff.mp render
      cases eq
      have present : ∀ b ∈ branches, (blockCommunication (toGProc b)).isSome := by
        intro b mem
        obtain ⟨m, _, branchResult⟩ := (mapM_members hb b).mp mem
        obtain ⟨suffix, hs, rfl⟩ := Option.map_eq_some'.mp branchResult
        obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp (ih hs)
        cases m.1 with
        | visible label =>
            cases label with
            | packet N => by_cases zero : netkatIsZero N = true <;>
                simp [MoveLabel.prefix, toGProc, blockCommunication, hout, zero]
            | rcfg => simp [MoveLabel.prefix, toGProc, blockCommunication, hout]
        | recv | send => rfl
      have choiceSupported (bs : List DyNetKAT)
          (ok : ∀ b ∈ bs, (blockCommunication (toGProc b)).isSome) :
          (blockCommunication (toGProc (choiceOf bs))).isSome := by
        induction bs with
        | nil => rfl
        | cons b rest ihBranches =>
            obtain ⟨first, hf⟩ := Option.isSome_iff_exists.mp (ok b (by simp))
            obtain ⟨last, hl⟩ := Option.isSome_iff_exists.mp
              (ihBranches (fun u hu => ok u (List.mem_cons_of_mem _ hu)))
            simp [choiceOf, toGProc, blockCommunication, hf, hl]
      exact choiceSupported branches present


end DyNetKAT.DyNetKAT
