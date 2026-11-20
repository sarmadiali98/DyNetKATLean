import DyNetKAT.DyNetKAT.Program

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

variable {schema : PacketSchema}

/-- A finite action word witnessed by one execution with consistent packet lists. -/
def SourceTrace (env : RecEnv schema) (p : DyNetKAT schema) (word : List (Action schema)) : Prop :=
  ∃ pending handled target, Steps env ⟨p, pending, handled⟩ word target

theorem Step.rebase {env : (RecEnv schema)} {c d : (Config schema)} {a : (Action schema)}
    (h : Step env c a d) (tail handled : List schema.Packet) :
    Step env ⟨c.proc, a.pendingFor tail, handled⟩ a ⟨d.proc, tail, a.handledAfter handled⟩ := by
  induction h with
  | cpol_seq_ok _ _ _ _ _ _ ev => exact .cpol_seq_ok _ _ _ _ tail handled ev
  | cpol_recv => exact .cpol_recv _ _ _ tail handled
  | cpol_send => exact .cpol_send _ _ _ tail handled
  | cpol_rcfg => exact .cpol_rcfg _ _ _ tail handled
  | cpol_choice_l _ _ _ _ _ _ _ _ _ ih => exact .cpol_choice_l _ _ _ _ _ _ _ _ ih
  | cpol_choice_r _ _ _ _ _ _ _ _ _ ih => exact .cpol_choice_r _ _ _ _ _ _ _ _ ih
  | cpol_par_l _ _ _ _ _ _ _ _ _ ih => exact .cpol_par_l _ _ _ _ _ _ _ _ ih
  | cpol_par_r _ _ _ _ _ _ _ _ _ ih => exact .cpol_par_r _ _ _ _ _ _ _ _ ih
  | cpol_left_merge _ _ _ _ _ _ _ _ _ ih => exact .cpol_left_merge _ _ _ _ _ _ _ _ ih
  | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .cpol_comm_merge_recv_send _ _ _ _ _ _ tail handled ih₁ ih₂
  | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .cpol_comm_merge_send_recv _ _ _ _ _ _ tail handled ih₁ ih₂
  | cpol_sync_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .cpol_sync_recv_send _ _ _ _ _ _ tail handled ih₁ ih₂
  | cpol_sync_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .cpol_sync_send_recv _ _ _ _ _ _ tail handled ih₁ ih₂
  | cpol_var _ _ _ _ _ _ _ _ lookup _ ih => exact .cpol_var _ _ _ _ _ _ _ _ lookup ih
  | cpol_project _ _ _ _ _ _ _ _ _ ih => exact .cpol_project _ _ _ _ _ _ _ _ ih
  | cpol_restrict _ _ _ _ _ _ _ _ allowed _ ih =>
      exact .cpol_restrict _ _ _ _ _ _ _ _ allowed ih

theorem Step.packetLists {env : (RecEnv schema)} {c d : (Config schema)} {a : (Action schema)}
    (h : Step env c a d) :
    c.pending = a.pendingFor d.pending ∧ d.handled = a.handledAfter c.handled := by
  induction h <;> first | exact ⟨rfl, rfl⟩ | assumption

theorem Steps.rebase {env : (RecEnv schema)} {c d : (Config schema)} {word : List (Action schema)}
    (h : Steps env c word d) (tail handled : List schema.Packet) :
    Steps env ⟨c.proc, word.foldr Action.pendingFor tail, handled⟩ word
      ⟨d.proc, tail, word.foldl (fun hl a => a.handledAfter hl) handled⟩ := by
  induction h generalizing handled with
  | nil => exact .nil _
  | cons _ _ _ a rest step _ ih =>
      exact .cons _ _ _ _ _ (step.rebase (rest.foldr Action.pendingFor tail) handled) (ih _)

/-- The action word fixes the consumed inputs and produced outputs. The unused
pending suffix and the previously handled packets can be chosen freely. -/
theorem sourceTrace_iff_packetLists {env : (RecEnv schema)} {p : (DyNetKAT schema)} {word : List (Action schema)}
    (tail handled : List schema.Packet) :
    SourceTrace env p word ↔ ∃ q,
      Steps env ⟨p, word.foldr Action.pendingFor tail, handled⟩ word
        ⟨q, tail, word.foldl (fun hl a => a.handledAfter hl) handled⟩ := by
  constructor
  · rintro ⟨_, _, d, steps⟩
    exact ⟨d.proc, steps.rebase tail handled⟩
  · rintro ⟨q, steps⟩
    exact ⟨_, _, ⟨q, _, _⟩, steps⟩

theorem sourceTrace_nil (env : RecEnv schema) (p : DyNetKAT schema) : SourceTrace env p [] :=
  ⟨[], [], ⟨p, [], []⟩, .nil _⟩

theorem sourceTrace_cons_iff {env : (RecEnv schema)} {p : (DyNetKAT schema)} {a : (Action schema)} {word : List (Action schema)} :
    SourceTrace env p (a :: word) ↔
      ∃ c d, c.proc = p ∧ Step env c a d ∧ SourceTrace env d.proc word := by
  constructor
  · rintro ⟨pt, hl, target, steps⟩
    cases steps with
    | cons _ next _ _ _ step rest => exact ⟨⟨p, pt, hl⟩, next, rfl, step, _, _, _, rest⟩
  · rintro ⟨c, d, rfl, step, pt, hl, target, rest⟩
    exact ⟨_, [], _, .cons _ _ _ _ _ (step.rebase (word.foldr Action.pendingFor []) [])
      (rest.rebase [] _)⟩

theorem sourceTrace_prefix_of_append {env : (RecEnv schema)} {c d : (Config schema)} {w : List (Action schema)}
    (h : Steps env c w d) {u v : List (Action schema)} (split : w = u ++ v) :
    SourceTrace env c.proc u := by
  induction h generalizing u with
  | nil => simp at split; obtain ⟨rfl, _⟩ := split; exact sourceTrace_nil ..
  | cons c next _ a _ step _ ih =>
      cases u with
      | nil => exact sourceTrace_nil ..
      | cons b u =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, split⟩ := split
          exact sourceTrace_cons_iff.mpr ⟨c, next, rfl, step, ih split⟩

theorem sourceTrace_project_iff {env : (RecEnv schema)} {p : (DyNetKAT schema)} {word : List (Action schema)} {n : Nat} :
    SourceTrace env (.project n p) word ↔ SourceTrace env p word ∧ word.length ≤ n := by
  constructor
  · rintro ⟨pt, hl, ⟨q, pt', hl'⟩, steps⟩
    obtain ⟨j, q', _, budget, run⟩ := steps_project_unwrap env word n p pt hl q pt' hl' steps
    exact ⟨⟨pt, hl, ⟨q', pt', hl'⟩, run⟩, by omega⟩
  · rintro ⟨⟨pt, hl, d, steps⟩, bound⟩
    obtain ⟨j, q, _, _, run⟩ := steps_project_lift env p pt hl word d steps n bound
    exact ⟨pt, hl, ⟨.project j q, d.pending, d.handled⟩, run⟩

namespace Program

variable {extended : Bool} {env : (RecEnv schema)} (p : Program extended env)

def Trace (word : List (Action schema)) : Prop := SourceTrace env p.term word

theorem trace_iff_reaches_residual (word : List (Action schema)) :
    p.Trace word ↔ ∃ (q : p.Residual), ∃ pt hl pt' hl',
      Steps env ⟨p.term, pt, hl⟩ word ⟨q.term, pt', hl'⟩ := by
  constructor
  · rintro ⟨pt, hl, d, run⟩
    exact ⟨p.afterTrace run, pt, hl, d.pending, d.handled, run⟩
  · rintro ⟨q, pt, hl, pt', hl', run⟩
    exact ⟨pt, hl, ⟨q.term, pt', hl'⟩, run⟩

variable {env : RecEnv} (p : Program extended env)

theorem Compiled.trace_iff (compiled : p.Compiled) (word : List Action) :
    p.Trace word ↔ ∃ pt hl d,
      GSteps compiled.graph ⟨compiled.graph.root, pt, hl⟩ word d := by
  constructor
  · rintro ⟨pt, hl, d, run⟩
    obtain ⟨q, run', _⟩ := steps_to_gsteps _ _ _ _ _ run _ compiled.corr
    exact ⟨pt, hl, ⟨q, d.pending, d.handled⟩, run'⟩
  · rintro ⟨pt, hl, d, run⟩
    obtain ⟨q, run', _⟩ := gsteps_to_steps _ _ _ _ _ run _ compiled.corr
    exact ⟨pt, hl, ⟨q, d.pending, d.handled⟩, run'⟩

end Program

/-- Canonical one-step observation, with one input when a packet is consumed. -/
def ActionStep (env : RecEnv schema) (p : DyNetKAT schema) (a : Action schema) (q : DyNetKAT schema) : Prop :=
  Step env ⟨p, a.pendingFor [], []⟩ a ⟨q, [], a.handledAfter []⟩

theorem sourceTrace_cons_actionStep {env : (RecEnv schema)} {p : (DyNetKAT schema)} {a : (Action schema)}
    {w : List (Action schema)} :
    SourceTrace env p (a :: w) ↔ ∃ q, ActionStep env p a q ∧ SourceTrace env q w := by
  rw [sourceTrace_cons_iff]
  constructor
  · rintro ⟨c, d, rfl, step, rest⟩
    exact ⟨d.proc, step.rebase [] [], rest⟩
  · rintro ⟨q, step, rest⟩
    exact ⟨⟨p, a.pendingFor [], []⟩, ⟨q, [], a.handledAfter []⟩, rfl, step, rest⟩

theorem sourceTrace_choice_iff {env : (RecEnv schema)} {p q : (DyNetKAT schema)} {w : List (Action schema)} :
    SourceTrace env (.choice p q) w ↔ SourceTrace env p w ∨ SourceTrace env q w := by
  cases w with
  | nil => exact ⟨fun _ => .inl (sourceTrace_nil ..), fun _ => sourceTrace_nil ..⟩
  | cons a w =>
      simp only [sourceTrace_cons_actionStep, ActionStep]
      constructor
      · rintro ⟨d, step, rest⟩
        exact (choice_step_inv _ _ _ _ _ _ _ _ _ step).elim
          (fun h => .inl ⟨d, h, rest⟩) (fun h => .inr ⟨d, h, rest⟩)
      · rintro (⟨d, step, rest⟩ | ⟨d, step, rest⟩)
        · exact ⟨d, .cpol_choice_l _ _ _ _ _ _ _ _ step, rest⟩
        · exact ⟨d, .cpol_choice_r _ _ _ _ _ _ _ _ step, rest⟩

theorem sourceTrace_movePrefix_iff {env : RecEnv} {l : MoveLabel} {p : DyNetKAT}
    {a : Action} {w : List Action} :
    SourceTrace env (l.prefix p) (a :: w) ↔
      l.Realizes (a.pendingFor []) [] a [] (a.handledAfter []) ∧ SourceTrace env p w := by
  rw [sourceTrace_cons_actionStep]
  simp [ActionStep, MoveLabel.prefix_step_iff]

theorem Bisimilar.sourceTrace_iff {env : RecEnv} {p q : DyNetKAT}
    (h : Bisimilar env p q) (w : List Action) :
    SourceTrace env p w ↔ SourceTrace env q w := by
  obtain ⟨R, bisim, related⟩ := h
  have transfer {p q : DyNetKAT} (h : R p q) : SourceTrace env p w → SourceTrace env q w := by
    induction w generalizing p q with
    | nil => exact fun _ => sourceTrace_nil ..
    | cons a w ih =>
        intro trace
        obtain ⟨p', step, rest⟩ := sourceTrace_cons_actionStep.mp trace
        obtain ⟨q', matched, rel⟩ := bisim.2 p q h _ _ a p' _ _ step
        exact sourceTrace_cons_actionStep.mpr ⟨q', matched, ih rel rest⟩
  exact ⟨transfer related, transfer (bisim.1 _ _ related)⟩

/-- The atomic prefix that emits exactly this SOS action. -/
def Action.atomicLabel : Action → MoveLabel
  | .packet i o => .visible (.packet (NormalForm.ofSummand (i, o)))
  | .rcfg x p => .visible (.rcfg x p)
  | .recv x p => .recv x p
  | .send x p => .send x p

theorem Equations.AtomicPrefix.exists_action {l : MoveLabel} (h : Equations.AtomicPrefix l) :
    ∃ a : Action, l = a.atomicLabel := by
  cases h with
  | packet i o => exact ⟨.packet i o, rfl⟩
  | rcfg x p => exact ⟨.rcfg x p, rfl⟩
  | recv x p => exact ⟨.recv x p, rfl⟩
  | send x p => exact ⟨.send x p, rfl⟩

private theorem atomicLabel_realizes_iff (l : Action) (pt hl : List CtxPkt) (a : Action)
    (pt' hl' : List CtxPkt) :
    l.atomicLabel.Realizes pt hl a pt' hl' ↔
      a = l ∧ pt = a.pendingFor pt' ∧ hl' = a.handledAfter hl := by
  cases l with
  | packet input output =>
      constructor
      · intro h
        cases h with
        | packet ev =>
            have sem := (historySemantics_singleton_iff_packetSemantics ..).mp ev
            obtain ⟨ei, eo⟩ := (ofSummand_sem ..).mp sem
            obtain rfl := (holdsComplete_iff_eq ..).mp ei
            subst_vars
            exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, rfl, rfl⟩
        exact .packet ((historySemantics_singleton_iff_packetSemantics ..).mpr
          ((ofSummand_sem ..).mpr ⟨(holdsComplete_iff_eq ..).mpr rfl, rfl⟩))
  | rcfg x p =>
      constructor
      · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, rfl, rfl⟩; exact .rcfg

  | recv x p =>
      constructor
      · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, rfl, rfl⟩; exact .recv
  | send x p =>
      constructor
      · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, rfl, rfl⟩; exact .send

theorem sourceTrace_atomicPrefix_iff {env : RecEnv} {l a : Action} {p : DyNetKAT}
    {word : List Action} :
    SourceTrace env (l.atomicLabel.prefix p) (a :: word) ↔ a = l ∧ SourceTrace env p word := by
  simp only [sourceTrace_movePrefix_iff, atomicLabel_realizes_iff, true_and, and_true]

end DyNetKAT.DyNetKAT
