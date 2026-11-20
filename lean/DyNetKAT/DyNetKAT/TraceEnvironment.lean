import DyNetKAT.DyNetKAT.SourceTrace

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : PacketSchema}

open DyNetKAT.NetKAT

/-- Change recursive names only. In particular channels and payloads are kept. -/
def DyNetKAT.renameRefs (f : Var → Var) : DyNetKAT schema → DyNetKAT schema
  | .deadlock => .deadlock
  | .var x => .var (f x)
  | .nSeq p q => .nSeq p (q.renameRefs f)
  | .recv x p q => .recv x p (q.renameRefs f)
  | .send x p q => .send x p (q.renameRefs f)
  | .rcfgPrefix x p q => .rcfgPrefix x p (q.renameRefs f)
  | .choice p q => .choice (p.renameRefs f) (q.renameRefs f)
  | .parallel p q => .parallel (p.renameRefs f) (q.renameRefs f)
  | .leftMerge p q => .leftMerge (p.renameRefs f) (q.renameRefs f)
  | .commMerge p q => .commMerge (p.renameRefs f) (q.renameRefs f)
  | .restrict L p => .restrict L (p.renameRefs f)
  | .project n p => .project n (p.renameRefs f)

private theorem recursiveVars_rename (f : Var → Var) (p : DyNetKAT schema) :
    recursiveVars (p.renameRefs f) = (recursiveVars p).image f := by
  induction p <;> simp [DyNetKAT.renameRefs, recursiveVars, *, Finset.image_union]

private theorem paperSyntax_rename (f : Var → Var) (p : DyNetKAT schema) (mode : Bool) :
    PaperSyntax mode (p.renameRefs f) ↔ PaperSyntax mode p := by
  induction p generalizing mode <;> simp [DyNetKAT.renameRefs, PaperSyntax, *]

private theorem guarded_rename (f : Var → Var) (p : DyNetKAT schema) :
    GuardedOccurrences (p.renameRefs f) ↔ GuardedOccurrences p := by
  induction p <;> simp [DyNetKAT.renameRefs, GuardedOccurrences, *]

/-- The target environment contains the renamed body at every renamed name. -/
private def RenamesEnv (f : Var → Var) (env target : RecEnv schema) : Prop :=
  ∀ x, target.lookup (f x) = (env.lookup x).map (DyNetKAT.renameRefs f)

private theorem rename_step {f : Var → Var} {env target : RecEnv schema}
    (compat : RenamesEnv f env target) {c d : Config schema} {a : Action schema}
    (h : Step env c a d) :
    Step target {c with proc := c.proc.renameRefs f} a {d with proc := d.proc.renameRefs f} := by
  induction h with
  | cpol_seq_ok _ _ _ _ _ _ ev => exact .cpol_seq_ok _ _ _ _ _ _ ev
  | cpol_send => exact .cpol_send _ _ _ _ _
  | cpol_recv => exact .cpol_recv _ _ _ _ _
  | cpol_rcfg => exact .cpol_rcfg _ _ _ _ _
  | cpol_choice_l _ _ _ _ _ _ _ _ _ ih => exact .cpol_choice_l _ _ _ _ _ _ _ _ ih
  | cpol_choice_r _ _ _ _ _ _ _ _ _ ih => exact .cpol_choice_r _ _ _ _ _ _ _ _ ih
  | cpol_par_l _ _ _ _ _ _ _ _ _ ih => exact .cpol_par_l _ _ _ _ _ _ _ _ ih
  | cpol_par_r _ _ _ _ _ _ _ _ _ ih => exact .cpol_par_r _ _ _ _ _ _ _ _ ih
  | cpol_left_merge _ _ _ _ _ _ _ _ _ ih => exact .cpol_left_merge _ _ _ _ _ _ _ _ ih
  | cpol_sync_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .cpol_sync_recv_send _ _ _ _ _ _ _ _ ih₁ ih₂
  | cpol_sync_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .cpol_sync_send_recv _ _ _ _ _ _ _ _ ih₁ ih₂
  | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ ih₁ ih₂
  | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ ih₁ ih₂
  | cpol_var x _ _ _ _ _ _ _ lookup _ ih =>
      exact .cpol_var _ _ _ _ _ _ _ _ (by rw [compat x, lookup]; rfl) ih
  | cpol_project _ _ _ _ _ _ _ _ _ ih => exact .cpol_project _ _ _ _ _ _ _ _ ih
  | cpol_restrict _ _ _ _ _ _ _ _ allowed _ ih =>
      exact .cpol_restrict _ _ _ _ _ _ _ _ allowed ih

private theorem rename_step_inv {f : Var → Var} {env target : RecEnv schema}
    (compat : RenamesEnv f env target) {c d : Config schema} {a : Action schema} (h : Step target c a d) :
    ∀ p, p.renameRefs f = c.proc →
      ∃ q, q.renameRefs f = d.proc ∧ Step env {c with proc := p} a {d with proc := q} := by
  induction h with
  | cpol_seq_ok _ _ _ _ _ _ ev =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨rfl, eq⟩ := eq
      exact ⟨_, eq, .cpol_seq_ok _ _ _ _ _ _ ev⟩
  | cpol_recv =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨rfl, rfl, eq⟩ := eq
      exact ⟨_, eq, .cpol_recv _ _ _ _ _⟩
  | cpol_send =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨rfl, rfl, eq⟩ := eq
      exact ⟨_, eq, .cpol_send _ _ _ _ _⟩
  | cpol_rcfg =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨rfl, rfl, eq⟩ := eq
      exact ⟨_, eq, .cpol_rcfg _ _ _ _ _⟩
  | cpol_choice_l _ _ _ _ _ _ _ _ _ ih =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨q, eq, inner⟩ := ih _ eq.1
      exact ⟨q, eq, .cpol_choice_l _ _ _ _ _ _ _ _ inner⟩
  | cpol_choice_r _ _ _ _ _ _ _ _ _ ih =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨q, eq, inner⟩ := ih _ eq.2
      exact ⟨q, eq, .cpol_choice_r _ _ _ _ _ _ _ _ inner⟩
  | cpol_par_l _ _ _ _ _ _ _ _ _ ih =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨q, same, inner⟩ := ih _ eq.1
      exact ⟨.parallel q _, congrArg₂ DyNetKAT.parallel same eq.2, .cpol_par_l _ _ _ _ _ _ _ _ inner⟩
  | cpol_par_r _ _ _ _ _ _ _ _ _ ih =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨q, same, inner⟩ := ih _ eq.2
      exact ⟨.parallel _ q, congrArg₂ DyNetKAT.parallel eq.1 same, .cpol_par_r _ _ _ _ _ _ _ _ inner⟩
  | cpol_left_merge _ _ _ _ _ _ _ _ _ ih =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨q, same, inner⟩ := ih _ eq.1
      exact ⟨.parallel q _, congrArg₂ DyNetKAT.parallel same eq.2,
        .cpol_left_merge _ _ _ _ _ _ _ _ inner⟩
  | cpol_sync_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨p, e₁, hp⟩ := ih₁ _ eq.1
      obtain ⟨q, e₂, hq⟩ := ih₂ _ eq.2
      exact ⟨.parallel p q, congrArg₂ DyNetKAT.parallel e₁ e₂,
        .cpol_sync_recv_send _ _ _ _ _ _ _ _ hp hq⟩
  | cpol_sync_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨p, e₁, hp⟩ := ih₁ _ eq.1
      obtain ⟨q, e₂, hq⟩ := ih₂ _ eq.2
      exact ⟨.parallel p q, congrArg₂ DyNetKAT.parallel e₁ e₂,
        .cpol_sync_send_recv _ _ _ _ _ _ _ _ hp hq⟩
  | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨p, e₁, hp⟩ := ih₁ _ eq.1
      obtain ⟨q, e₂, hq⟩ := ih₂ _ eq.2
      exact ⟨.parallel p q, congrArg₂ DyNetKAT.parallel e₁ e₂,
        .cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ hp hq⟩
  | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨p, e₁, hp⟩ := ih₁ _ eq.1
      obtain ⟨q, e₂, hq⟩ := ih₂ _ eq.2
      exact ⟨.parallel p q, congrArg₂ DyNetKAT.parallel e₁ e₂,
        .cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ hp hq⟩
  | cpol_var name body _ _ _ _ _ _ lookup _ ih =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      rename_i x
      rw [← eq, compat] at lookup
      obtain ⟨originalBody, definition, same⟩ := Option.map_eq_some_iff.mp lookup
      obtain ⟨q, eq, step⟩ := ih originalBody same
      exact ⟨q, eq, .cpol_var _ _ _ _ _ _ _ _ definition step⟩
  | cpol_project n _ _ _ _ _ _ _ _ ih =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨rfl, eq⟩ := eq
      obtain ⟨q, same, step⟩ := ih _ eq
      exact ⟨.project n q, congrArg _ same, .cpol_project _ _ _ _ _ _ _ _ step⟩
  | cpol_restrict L _ _ _ _ _ _ _ allowed _ ih =>
      intro original eq
      cases original <;> simp [DyNetKAT.renameRefs] at eq
      obtain ⟨rfl, eq⟩ := eq
      obtain ⟨q, same, step⟩ := ih _ eq
      exact ⟨.restrict _ q, congrArg _ same, .cpol_restrict _ _ _ _ _ _ _ _ allowed step⟩

private theorem rename_trace {f : Var → Var} {env target : RecEnv schema}
    (compat : RenamesEnv f env target) (p : DyNetKAT schema) (w : List (Action schema)) :
    SourceTrace target (p.renameRefs f) w ↔ SourceTrace env p w := by
  induction w generalizing p with
  | nil => exact ⟨fun _ => sourceTrace_nil .., fun _ => sourceTrace_nil ..⟩
  | cons a w ih =>
      simp only [sourceTrace_cons_actionStep]
      constructor
      · rintro ⟨q, step, rest⟩
        obtain ⟨original, rfl, inner⟩ := rename_step_inv compat step p rfl
        exact ⟨original, inner, (ih _).mp rest⟩
      · rintro ⟨q, step, rest⟩
        exact ⟨q.renameRefs f, rename_step compat step, (ih _).mpr rest⟩

private theorem rename_admissible {f : Var → Var} {env target : RecEnv schema}
    (compat : RenamesEnv f env target) {p : DyNetKAT schema} {mode : Bool}
    (admitted : PaperAdmissible mode env p) :
    PaperAdmissible true target (p.renameRefs f) := by
  have sorted {q : DyNetKAT schema} (h : PaperSyntax mode q) : PaperSyntax true q := by
    cases mode
    · exact h.of_base
    · exact h
  refine (paperAdmissible_iff ..).mpr ⟨(paperSyntax_rename ..).mpr (sorted admitted.2.1), ?_⟩
  intro x reach
  have inherited : ∃ y, f y = x ∧ ReachableVar env p y := by
    induction reach with
    | direct mem =>
        rw [recursiveVars_rename] at mem
        obtain ⟨y, occurs, eq⟩ := Finset.mem_image.mp mem
        exact ⟨y, eq, .direct occurs⟩
    | throughDefinition _ lookup mem ih =>
        obtain ⟨y, rfl, source⟩ := ih
        rw [compat] at lookup
        obtain ⟨body, definition, rfl⟩ := Option.map_eq_some_iff.mp lookup
        rw [recursiveVars_rename] at mem
        obtain ⟨v, occurs, eq⟩ := Finset.mem_image.mp mem
        exact ⟨v, eq, .throughDefinition source definition occurs⟩
  obtain ⟨y, rfl, reaches⟩ := inherited
  obtain ⟨body, definition, guarded⟩ := admitted.1.2 y reaches
  have lookup : target.lookup (f y) = some (body.renameRefs f) := by rw [compat, definition]; rfl
  exact ⟨_, ⟨lookup, (paperSyntax_rename ..).mpr (sorted (admitted.2.2 y body reaches definition)),
      (typedPaperGuarded_iff_guardedOccurrences _).mpr ((guarded_rename ..).mpr guarded)⟩,
    fun q defn => RecEnv.lookup_unique defn.1 lookup⟩

private def namespaceName (tag : Char) (name : Var) : Var := String.mk (tag :: name.data)

/-- Two declaration systems coexist after changing their recursive names apart. -/
def RecEnv.disjoint (left right : RecEnv schema) : RecEnv schema := fun name =>
  match name.data with
  | 'l' :: xs => (left.lookup (String.mk xs)).map (DyNetKAT.renameRefs (namespaceName 'l'))
  | 'r' :: xs => (right.lookup (String.mk xs)).map (DyNetKAT.renameRefs (namespaceName 'r'))
  | _ => none

private theorem leftEnv {left right : RecEnv schema} :
    RenamesEnv (namespaceName 'l') left (left.disjoint right) := by
  intro x
  cases x
  rfl

private theorem rightEnv {left right : RecEnv schema} :
    RenamesEnv (namespaceName 'r') right (left.disjoint right) := by
  intro x
  cases x
  rfl

namespace Program

variable {mode : Bool} {env : RecEnv schema}

def inLeft (p : Program mode env) (other : RecEnv schema) : Program true (env.disjoint other) :=
  ⟨p.term.renameRefs (namespaceName 'l'), rename_admissible leftEnv p.admissible⟩

def inRight (p : Program mode env) (other : RecEnv schema) : Program true (other.disjoint env) :=
  ⟨p.term.renameRefs (namespaceName 'r'), rename_admissible rightEnv p.admissible⟩

/-- Source choice between two admissible programs in the same environment. -/
def choice (p q : Program mode env) : Program mode env := by
  refine ⟨.choice p.term q.term, (paperAdmissible_iff ..).mpr
    ⟨⟨p.admissible.2.1, q.admissible.2.1⟩, ?_⟩⟩
  intro x hx
  have origins : ReachableVar env p.term x ∨ ReachableVar env q.term x := by
    induction hx with
    | direct mem => exact (Finset.mem_union.mp mem).imp ReachableVar.direct ReachableVar.direct
    | throughDefinition _ lookup mem ih =>
        exact ih.imp (fun h => .throughDefinition h lookup mem)
          (fun h => .throughDefinition h lookup mem)
  exact origins.elim (((paperAdmissible_iff ..).mp p.admissible).2 x)
    (((paperAdmissible_iff ..).mp q.admissible).2 x)

theorem choice_trace (p q : Program mode env) (w : List (Action schema)) :
    (p.choice q).Trace w ↔ p.Trace w ∨ q.Trace w := sourceTrace_choice_iff

theorem inLeft_trace (p : Program mode env) (other : RecEnv schema) (w : List (Action schema)) :
    (p.inLeft other).Trace w ↔ p.Trace w := rename_trace leftEnv _ _

theorem inRight_trace (p : Program mode env) (other : RecEnv schema) (w : List (Action schema)) :
    (p.inRight other).Trace w ↔ p.Trace w := rename_trace rightEnv _ _

end Program
end DyNetKAT.DyNetKAT
