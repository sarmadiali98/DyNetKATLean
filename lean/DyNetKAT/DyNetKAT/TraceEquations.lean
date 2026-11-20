import DyNetKAT.DyNetKAT.SourceTrace

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : PacketSchema}

open DyNetKAT.NetKAT

/-- Both sends and receives remain observable here, so the trace equivalence
can be used before restriction and synchronization. -/
def TraceEquivalent {schema : PacketSchema} (env : RecEnv schema) (p q : DyNetKAT schema) : Prop :=
  ∀ w, SourceTrace env p w ↔ SourceTrace env q w

theorem trace_a16 {schema : PacketSchema} (env : RecEnv schema) (l : MoveLabel schema)
    (p q : DyNetKAT schema) :
    TraceEquivalent env (l.prefix (.choice p q)) (.choice (l.prefix p) (l.prefix q)) := by
  intro w
  cases w with
  | nil => exact ⟨fun _ => sourceTrace_nil .., fun _ => sourceTrace_nil ..⟩
  | cons a w =>
      simp only [sourceTrace_movePrefix_iff, sourceTrace_choice_iff]
      tauto

private inductive Combination
  | parallel | leftMerge | commMerge

private def Combination.term : Combination → DyNetKAT schema → DyNetKAT schema → DyNetKAT schema
  | .parallel => .parallel
  | .leftMerge => .leftMerge
  | .commMerge => .commMerge

private inductive Turn {schema : PacketSchema} : Option (Action schema) → Option (Action schema) → Action schema → Prop
  | left : Turn (some a) none a
  | right : Turn none (some a) a
  | recvSend : Turn (some (.recv x p)) (some (.send x p)) (.rcfg x p)
  | sendRecv : Turn (some (.send x p)) (some (.recv x p)) (.rcfg x p)

private def Combination.permits : Combination → Option (Action schema) → Option (Action schema) → Prop
  | .parallel, _, _ => True
  | .leftMerge, some _, none => True
  | .commMerge, some _, some _ => True
  | _, _, _ => False

private def Follows (env : RecEnv schema) (p : DyNetKAT schema) (a : Option (Action schema)) (q : DyNetKAT schema) : Prop :=
  match a with
  | none => q = p
  | some a => ActionStep env p a q

private theorem combine_step_iff {env : RecEnv schema} {m : Combination} {p q r : DyNetKAT schema}
    {a : Action schema} :
    ActionStep env (m.term p q) a r ↔
      ∃ x y u v, Turn u v a ∧ m.permits u v ∧
        Follows env p u x ∧ Follows env q v y ∧ r = .parallel x y := by
  constructor
  · intro step
    cases m with
    | parallel =>
        cases step with
        | cpol_par_l _ _ _ _ _ _ _ _ h => exact ⟨_, _, _, _, .left, trivial, h, rfl, rfl⟩
        | cpol_par_r _ _ _ _ _ _ _ _ h => exact ⟨_, _, _, _, .right, trivial, rfl, h, rfl⟩
        | cpol_sync_recv_send _ _ _ _ _ _ _ _ h k =>
            exact ⟨_, _, _, _, .recvSend, trivial, h, k, rfl⟩
        | cpol_sync_send_recv _ _ _ _ _ _ _ _ h k =>
            exact ⟨_, _, _, _, .sendRecv, trivial, h, k, rfl⟩
    | leftMerge =>
        cases step with
        | cpol_left_merge _ _ _ _ _ _ _ _ h => exact ⟨_, _, _, _, .left, trivial, h, rfl, rfl⟩
    | commMerge =>
        cases step with
        | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ h k =>
            exact ⟨_, _, _, _, .recvSend, trivial, h, k, rfl⟩
        | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ h k =>
            exact ⟨_, _, _, _, .sendRecv, trivial, h, k, rfl⟩
  · rintro ⟨x, y, u, v, turn, allowed, first, second, rfl⟩
    cases turn with
    | left =>
        obtain rfl : y = q := second
        cases m with
        | parallel => exact .cpol_par_l _ _ _ _ _ _ _ _ first
        | leftMerge => exact .cpol_left_merge _ _ _ _ _ _ _ _ first
        | commMerge => exact False.elim allowed
    | right =>
        obtain rfl : x = p := first
        cases m with
        | parallel => exact .cpol_par_r _ _ _ _ _ _ _ _ second
        | leftMerge | commMerge => exact False.elim allowed
    | recvSend =>
        cases m with
        | parallel => exact .cpol_sync_recv_send _ _ _ _ _ _ [] [] first second
        | leftMerge => exact False.elim allowed
        | commMerge => exact .cpol_comm_merge_recv_send _ _ _ _ _ _ [] [] first second
    | sendRecv =>
        cases m with
        | parallel => exact .cpol_sync_send_recv _ _ _ _ _ _ [] [] first second
        | leftMerge => exact False.elim allowed
        | commMerge => exact .cpol_comm_merge_send_recv _ _ _ _ _ _ [] [] first second

private def addAction (a : Option (Action schema)) (w : List (Action schema)) : List (Action schema) :=
  match a with
  | none => w
  | some a => a :: w

private inductive Schedule {schema : PacketSchema} : Combination → List (Action schema) → List (Action schema) → List (Action schema) → Prop
  | nil (mode) : Schedule mode [] [] []
  | cons (mode) (turn : Turn u v a) (allowed : mode.permits u v)
      (rest : Schedule .parallel l r w) :
      Schedule mode (addAction u l) (addAction v r) (a :: w)

private theorem trace_addAction {env : RecEnv schema} {p : DyNetKAT schema} {a : Option (Action schema)}
    {w : List (Action schema)} :
    SourceTrace env p (addAction a w) ↔
      ∃ q, Follows env p a q ∧ SourceTrace env q w := by
  cases a with
  | some a => exact sourceTrace_cons_actionStep
  | none => simp [addAction, Follows]

private theorem trace_combination_iff {env : RecEnv schema} {mode : Combination} {p q : DyNetKAT schema}
    {w : List (Action schema)} :
    SourceTrace env (mode.term p q) w ↔
      ∃ u v, Schedule mode u v w ∧ SourceTrace env p u ∧ SourceTrace env q v := by
  induction w generalizing mode p q with
  | nil => exact ⟨fun _ => ⟨[], [], .nil _, sourceTrace_nil .., sourceTrace_nil ..⟩,
      fun _ => sourceTrace_nil ..⟩
  | cons a w ih =>
      constructor
      · intro trace
        obtain ⟨s, step, rest⟩ := sourceTrace_cons_actionStep.mp trace
        obtain ⟨x, y, i, j, turn, allowed, sx, sy, rfl⟩ := combine_step_iff.mp step
        obtain ⟨u, v, schedule, tu, tv⟩ := (ih (mode := .parallel)).mp rest
        exact ⟨_, _, .cons _ turn allowed schedule,
          trace_addAction.mpr ⟨x, sx, tu⟩, trace_addAction.mpr ⟨y, sy, tv⟩⟩
      · rintro ⟨u, v, schedule, left, right⟩
        cases schedule with
        | cons _ turn allowed schedule =>
            obtain ⟨x, sx, tu⟩ := trace_addAction.mp left
            obtain ⟨y, sy, tv⟩ := trace_addAction.mp right
            exact sourceTrace_cons_actionStep.mpr
              ⟨.parallel x y, combine_step_iff.mpr ⟨x, y, _, _, turn, allowed, sx, sy, rfl⟩,
                (ih (mode := .parallel)).mpr ⟨_, _, schedule, tu, tv⟩⟩

private theorem trace_combination_congr {env : RecEnv schema} {mode : Combination}
    {p p' q q' : DyNetKAT schema} (hp : TraceEquivalent env p p') (hq : TraceEquivalent env q q') :
    TraceEquivalent env (mode.term p q) (mode.term p' q') := by
  intro w
  rw [trace_combination_iff, trace_combination_iff]
  constructor
  · rintro ⟨u, v, plan, first, second⟩
    exact ⟨u, v, plan, (hp u).mp first, (hq v).mp second⟩
  · rintro ⟨u, v, plan, first, second⟩
    exact ⟨u, v, plan, (hp u).mpr first, (hq v).mpr second⟩

theorem sourceTrace_restrict_iff {env : RecEnv schema} {L : Set (CommunicationAction schema)}
    {p : DyNetKAT schema} {w : List (Action schema)} :
    SourceTrace env (.restrict L p) w ↔ SourceTrace env p w ∧
      ∀ a ∈ w, actionAllowed L a := by
  induction w generalizing p with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, and_true]
           exact ⟨fun _ => sourceTrace_nil .., fun _ => sourceTrace_nil ..⟩
  | cons a w ih =>
      simp only [sourceTrace_cons_actionStep]
      constructor
      · rintro ⟨r, step, rest⟩
        obtain ⟨q, rfl, allowed, inner⟩ := restrict_step_inv _ _ _ _ _ _ _ _ _ step
        obtain ⟨run, allowedRest⟩ := ih.mp rest
        exact ⟨⟨q, inner, run⟩, fun k hk =>
          (List.mem_cons.mp hk).elim (fun e => e ▸ allowed) (allowedRest k)⟩
      · rintro ⟨⟨q, inner, run⟩, allowed⟩
        exact ⟨.restrict L q, .cpol_restrict _ _ _ _ _ _ _ _ (allowed a (by simp)) inner,
          ih.mpr ⟨run, fun k hk => allowed k (List.mem_cons_of_mem _ hk)⟩⟩

/-- Definition 15. Retain the Figure 11 derivations, close under the same
process contexts and AIP, and add the prefix distributivity axiom (26). -/
inductive TraceDerives {schema : PacketSchema} (env : RecEnv schema) : DyNetKAT schema → DyNetKAT schema → Prop
  | strong : Derives env p q → TraceDerives env p q
  | a16 (l : MoveLabel schema) (p q : DyNetKAT schema) :
      TraceDerives env (l.prefix (.choice p q)) (.choice (l.prefix p) (l.prefix q))
  | symm : TraceDerives env p q → TraceDerives env q p
  | trans : TraceDerives env p q → TraceDerives env q r → TraceDerives env p r
  | prefixCongr (l : MoveLabel schema) : TraceDerives env p q → TraceDerives env (l.prefix p) (l.prefix q)
  | choiceCongr : TraceDerives env p p' → TraceDerives env q q' →
      TraceDerives env (.choice p q) (.choice p' q')
  | parallelCongr : TraceDerives env p p' → TraceDerives env q q' →
      TraceDerives env (.parallel p q) (.parallel p' q')
  | leftMergeCongr : TraceDerives env p p' → TraceDerives env q q' →
      TraceDerives env (.leftMerge p q) (.leftMerge p' q')
  | commMergeCongr : TraceDerives env p p' → TraceDerives env q q' →
      TraceDerives env (.commMerge p q) (.commMerge p' q')
  | restrictCongr (L : Set (CommunicationAction schema)) : TraceDerives env p q →
      TraceDerives env (.restrict L p) (.restrict L q)
  | projectCongr (n : Nat) : TraceDerives env p q → TraceDerives env (.project n p) (.project n q)
  | aip : ImageFiniteFrom env p → ImageFiniteFrom env q →
      (∀ n : Nat, TraceDerives env (.project n p) (.project n q)) → TraceDerives env p q

theorem TraceDerives.sound {env : RecEnv schema} {p q : DyNetKAT schema} (derives : TraceDerives env p q) :
    TraceEquivalent env p q := by
  induction derives with
  | strong h => exact h.sound.sourceTrace_iff
  | a16 l p q => exact trace_a16 env l p q
  | symm _ ih => exact fun w => (ih w).symm
  | trans _ _ ih₁ ih₂ => exact fun w => (ih₁ w).trans (ih₂ w)
  | prefixCongr l _ ih =>
      intro w
      cases w with
      | nil => exact ⟨fun _ => sourceTrace_nil .., fun _ => sourceTrace_nil ..⟩
      | cons a w => simp only [sourceTrace_movePrefix_iff, ih w]
  | choiceCongr _ _ ih₁ ih₂ => intro w; simp only [sourceTrace_choice_iff, ih₁ w, ih₂ w]
  | parallelCongr _ _ ih₁ ih₂ => exact trace_combination_congr (mode := .parallel) ih₁ ih₂
  | leftMergeCongr _ _ ih₁ ih₂ => exact trace_combination_congr (mode := .leftMerge) ih₁ ih₂
  | commMergeCongr _ _ ih₁ ih₂ => exact trace_combination_congr (mode := .commMerge) ih₁ ih₂
  | restrictCongr L _ ih => intro w; simp only [sourceTrace_restrict_iff, ih w]
  | projectCongr n _ ih => intro w; simp only [sourceTrace_project_iff, ih w]
  | aip _ _ _ ih =>
      intro w
      simpa only [sourceTrace_project_iff, Nat.le_refl, and_true] using ih w.length w


theorem TraceDerives.ofNoAIP {env : RecEnv schema} {p q : DyNetKAT schema}
    (h : DerivesNoAIP env p q) : TraceDerives env p q := .strong (.ofNoAIP h)

variable [DiagramLayout schema]

private def renderTraceWord : List (Action schema) → DyNetKAT schema
  | [] => .deadlock
  | a :: w => a.atomicLabel.prefix (renderTraceWord w)

private def traceWordSum (ws : List (List (Action schema))) : DyNetKAT schema :=
  choiceOf (ws.map renderTraceWord)

private def prefixWords (a : Action schema) (ws : List (List (Action schema))) : List (List (Action schema)) :=
  ws.map (a :: ·) ++ [[a]]

private theorem prefix_wordSum (env : RecEnv schema) (a : Action schema) (ws : List (List (Action schema))) :
    TraceDerives env (a.atomicLabel.prefix (traceWordSum ws)) (traceWordSum (prefixWords a ws)) := by
  induction ws with
  | nil => exact .ofNoAIP (.symm (.a5 _))
  | cons w rest ih =>
      exact .trans (.a16 _ _ _) (.choiceCongr (.strong (Derives.refl _ _)) ih)

private theorem traceWordSum_append (env : RecEnv schema) (xs ys : List (List (Action schema))) :
    TraceDerives env (.choice (traceWordSum xs) (traceWordSum ys)) (traceWordSum (xs ++ ys)) :=
  .ofNoAIP (by simpa only [traceWordSum, List.map_append] using
    choiceOf_append env (xs.map renderTraceWord) (ys.map renderTraceWord))

private theorem traceWordSum_eq (env : RecEnv schema) {xs ys : List (List (Action schema))}
    (h : ∀ w, w ∈ xs ↔ w ∈ ys) :
    TraceDerives env (traceWordSum xs) (traceWordSum ys) :=
  .ofNoAIP (choiceOf_derives_of_mem_iff env (by intro p; simp only [List.mem_map, h]))

private theorem mem_prefixWords {env : RecEnv schema} {p : DyNetKAT schema} {a x : Action schema}
    {ws : List (List (Action schema))} (h : ∀ w, w ≠ [] → (w ∈ ws ↔ SourceTrace env p w))
    (w : List (Action schema)) :
    x :: w ∈ prefixWords a ws ↔ SourceTrace env (a.atomicLabel.prefix p) (x :: w) := by
  rw [sourceTrace_atomicPrefix_iff]
  cases w with
  | nil => simp [prefixWords, List.mem_map, eq_comm, sourceTrace_nil]
  | cons b w =>
      simp only [prefixWords, List.mem_append, List.mem_map, List.mem_singleton, List.cons.injEq,
        List.cons_ne_nil, and_false, or_false]
      constructor
      · rintro ⟨v, mem, rfl, rfl⟩
        exact ⟨rfl, (h _ (by simp)).mp mem⟩
      · rintro ⟨rfl, trace⟩
        exact ⟨b :: w, (h _ (by simp)).mpr trace, rfl, rfl⟩

private def Represents (env : RecEnv schema) (p : DyNetKAT schema) (ws : List (List (Action schema))) : Prop :=
  [] ∉ ws ∧ ∀ w, w ≠ [] → (w ∈ ws ↔ SourceTrace env p w)

/-- Every finite projection has an equational word sum that lists exactly
its nonempty traces. A16 is used to distribute prefixes over continuations. -/
private theorem project_wordSum (env : RecEnv schema) (n : Nat) {p : DyNetKAT schema}
    (hp : WellFormed env p) :
    ∃ ws, TraceDerives env (.project n p) (traceWordSum ws) ∧
      Represents env (.project n p) ws := by
  induction n generalizing p with
  | zero =>
      refine ⟨[], .ofNoAIP (.projectZero _), by simp, ?_⟩
      intro w nonempty
      simp only [List.not_mem_nil, false_iff, sourceTrace_project_iff, Nat.le_zero_eq,
        List.length_eq_zero_iff]
      exact fun h => nonempty h.2
  | succ n ih =>
      obtain ⟨xs, derives, closed⟩ := hp.exists_headNormalForm_closed
      have heads : TraceDerives env (.project (n + 1) p) (xs.project (n + 1)).render :=
        .ofNoAIP (.trans (.projectCongr _ derives) (HeadNormalForm.project_correct ..))
      have normalizeHeads (xs : HeadNormalForm schema)
          (closed : ∀ b ∈ xs, WellFormed env b.continuation) :
          ∃ ws, TraceDerives env (xs.project (n + 1)).render (traceWordSum ws) ∧
            Represents env (xs.project (n + 1)).render ws := by
        induction xs with
        | nil =>
            refine ⟨[], .strong (Derives.refl ..), by simp, ?_⟩
            intro w nonempty
            cases w with
            | nil => exact False.elim (nonempty rfl)
            | cons a w =>
                simp only [List.not_mem_nil, false_iff, sourceTrace_cons_actionStep]
                rintro ⟨q, step, _⟩
                exact deadlock_no_step _ _ _ _ _ step
        | cons b xs tailIH =>
            obtain ⟨a, label⟩ := b.atomic.exists_action
            obtain ⟨ws, ds, _, exactWords⟩ := ih (closed b (by simp))
            obtain ⟨vs, dt, empty, exactTail⟩ :=
              tailIH (fun c hc => closed c (List.mem_cons_of_mem _ hc))
            let front := a.atomicLabel.prefix (.project n b.continuation)
            have renderHead : (HeadNormalForm.project (n + 1) (b :: xs)).render =
                .choice front (HeadNormalForm.project (n + 1) xs).render := by
              change DyNetKAT.choice (b.label.prefix (.project n b.continuation))
                (HeadNormalForm.project (n + 1) xs).render =
                  DyNetKAT.choice front (HeadNormalForm.project (n + 1) xs).render
              rw [label]
            rw [renderHead]
            refine ⟨prefixWords a ws ++ vs, ?_, ?_, ?_⟩
            · exact .trans (.choiceCongr (.trans (.prefixCongr _ ds) (prefix_wordSum ..)) dt)
                (traceWordSum_append ..)
            · simpa [prefixWords, List.mem_map] using empty
            · intro w nonempty
              cases w with
              | nil => exact False.elim (nonempty rfl)
              | cons x w =>
                  rw [List.mem_append, mem_prefixWords exactWords, exactTail _ (by simp),
                    sourceTrace_choice_iff]
      obtain ⟨ws, derivation, empty, exactWords⟩ := normalizeHeads xs closed
      exact ⟨ws, .trans heads derivation, empty,
        fun w hw => (exactWords w hw).trans (heads.sound w).symm⟩

/-- Trace completeness on closed guarded processes. There is one finite
word-sum derivation at each projection depth, and AIP combines them.
No finite global derivative space or support set is required. -/
theorem TraceDerives.complete {env : RecEnv schema} {p q : DyNetKAT schema}
    (hp : WellFormed env p) (hq : WellFormed env q) (traces : TraceEquivalent env p q) :
    TraceDerives env p q := by
  apply TraceDerives.aip hp.imageFiniteFrom hq.imageFiniteFrom
  intro n
  obtain ⟨xs, dx, hx, ex⟩ := project_wordSum env n hp
  obtain ⟨ys, dy, hy, ey⟩ := project_wordSum env n hq
  refine .trans dx (.trans (traceWordSum_eq env ?_) (.symm dy))
  intro w
  by_cases empty : w = []
  · subst w
    exact ⟨fun h => (hx h).elim, fun h => (hy h).elim⟩
  · rw [ex w empty, ey w empty]
    simp only [sourceTrace_project_iff, traces w]

theorem TraceDerives.iff_traces {env : RecEnv schema} {p q : DyNetKAT schema}
    (hp : WellFormed env p) (hq : WellFormed env q) :
    TraceDerives env p q ↔ TraceEquivalent env p q :=
  ⟨TraceDerives.sound, TraceDerives.complete hp hq⟩

end DyNetKAT.DyNetKAT
