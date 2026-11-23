import DyNetKATLean.Core.ProcessGraph
import NetKATLean.Core.Decision

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : PacketSchema}

open DyNetKAT.NetKAT

/-- A policy denotes all packet actions in its relation. Reconfigurations
    have a single action and leave both packet lists unchanged. -/
inductive SequentialLabel (schema : PacketSchema := ctxSchema) where
  | packet (policy : NetKAT schema)
  | rcfg (channel : Channel) (policy : NetKAT schema)
  deriving DecidableEq

inductive MoveLabel (schema : PacketSchema := ctxSchema) where
  | visible (label : SequentialLabel schema)
  | recv (channel : Channel) (policy : NetKAT schema)
  | send (channel : Channel) (policy : NetKAT schema)
  deriving DecidableEq

/-- Instantiate a symbolic edge with exactly the packet-list effects of
    the corresponding prefix in the SOS. -/
inductive MoveLabel.Realizes {schema : PacketSchema} :
    MoveLabel schema → List schema.Packet → List schema.Packet → Action schema →
      List schema.Packet → List schema.Packet → Prop
  | packet (h : HistorySemantics p (History.singleton σ) (History.singleton τ)) :
      Realizes (.visible (.packet p)) (σ :: pt) hl (.packet σ τ) pt (τ :: hl)
  | rcfg : Realizes (.visible (.rcfg x p)) pt hl (.rcfg x p) pt hl
  | recv : Realizes (.recv x p) pt hl (.recv x p) pt hl
  | send : Realizes (.send x p) pt hl (.send x p) pt hl

abbrev SymbolicMove (schema : PacketSchema := ctxSchema) := (MoveLabel schema) × (GProc schema)

/-- Soundness and completeness of a symbolic row at every configuration
    whose process is p. -/
def MovesExact (G : ProcessGraph schema) (p : GProc schema) (row : List (SymbolicMove schema)) : Prop :=
  ∀ pt hl a q pt' hl', GStep G ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩ ↔
    ∃ l, (l, q) ∈ row ∧ MoveLabel.Realizes l pt hl a pt' hl'

private def syncMoveWith {α : Type} (join : α → α → α)
    (left right : (MoveLabel schema) × α) : Option ((MoveLabel schema) × α) :=
  match left, right with
  | (.send x p, u), (.recv y q, v) | (.recv x p, u), (.send y q, v) =>
      if x = y ∧ p = q then some (.visible (.rcfg x p), join u v) else none
  | _, _ => none

private def syncMovesWith {α : Type} (join : α → α → α)
    (left right : List ((MoveLabel schema) × α)) : List ((MoveLabel schema) × α) :=
  left.flatMap fun l => right.filterMap (syncMoveWith join l)

private abbrev syncMove := syncMoveWith (schema := schema) (@GProc.parallel schema)
private abbrev syncMoves := syncMovesWith (schema := schema) (@GProc.parallel schema)

private theorem mem_syncMoves {left right : List (SymbolicMove schema)} {l : MoveLabel schema} {q : GProc schema} :
    (l, q) ∈ syncMoves left right ↔
      ∃ x N u v, l = .visible (.rcfg x N) ∧ q = .parallel u v ∧
        (((.send x N, u) ∈ left ∧ (.recv x N, v) ∈ right) ∨
         ((.recv x N, u) ∈ left ∧ (.send x N, v) ∈ right)) := by
  simp only [syncMovesWith, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨⟨l₁, u⟩, h₁, ⟨l₂, v⟩, h₂, h⟩
    cases l₁ <;> cases l₂ <;> simp [syncMoveWith] at h
    · obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, rfl, rfl, Or.inr ⟨h₁, h₂⟩⟩
    · obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, rfl, rfl, Or.inl ⟨h₁, h₂⟩⟩
  · rintro ⟨x, N, u, v, rfl, rfl, ⟨hl, hr⟩ | ⟨hl, hr⟩⟩
    · exact ⟨_, hl, _, hr, by simp [syncMoveWith]⟩
    · exact ⟨_, hl, _, hr, by simp [syncMoveWith]⟩

private def leftMoves (p : GProc schema) (row : List (SymbolicMove schema)) : List (SymbolicMove schema) :=
  row.map fun (l, q) => (l, .parallel q p)

private def rightMoves (p : GProc schema) (row : List (SymbolicMove schema)) : List (SymbolicMove schema) :=
  row.map fun (l, q) => (l, .parallel p q)

private def projectedMoves (n : Nat) (row : List (SymbolicMove schema)) : List (SymbolicMove schema) :=
  row.map fun (l, q) => (l, .project n q)

private theorem mem_leftMoves {p q : GProc schema} {l : MoveLabel schema} {row : List (SymbolicMove schema)} :
    (l, q) ∈ leftMoves p row ↔ ∃ u, (l, u) ∈ row ∧ q = .parallel u p := by
  simp only [leftMoves, List.mem_map]
  constructor
  · rintro ⟨⟨_, u⟩, hu, he⟩
    cases he
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, hu, rfl⟩

private theorem mem_rightMoves {p q : GProc schema} {l : MoveLabel schema} {row : List (SymbolicMove schema)} :
    (l, q) ∈ rightMoves p row ↔ ∃ u, (l, u) ∈ row ∧ q = .parallel p u := by
  simp only [rightMoves, List.mem_map]
  constructor
  · rintro ⟨⟨_, u⟩, hu, he⟩
    cases he
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, hu, rfl⟩

private theorem mem_projectedMoves {n : Nat} {q : GProc schema} {l : MoveLabel schema}
    {row : List (SymbolicMove schema)} :
    (l, q) ∈ projectedMoves n row ↔ ∃ u, (l, u) ∈ row ∧ q = .project n u := by
  simp only [projectedMoves, List.mem_map]
  constructor
  · rintro ⟨⟨_, u⟩, hu, he⟩
    cases he
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, hu, rfl⟩

/-- A restriction site is addressed relative to the term being scanned.
False selects the left or sole child and true selects the right child.
The result is true exactly for a blocked communication action. -/
abbrev RestrictionChecks (schema : PacketSchema := ctxSchema) := List Bool → CommunicationAction schema → Bool

def RestrictionChecks.child (right : Bool) : RestrictionChecks schema → RestrictionChecks schema :=
  fun check path => check (right :: path)

private def MoveLabel.allowed (blocked : CommunicationAction schema → Bool) : MoveLabel schema → Bool
  | .visible _ => true
  | .recv x p => !blocked (.recv x p)
  | .send x p => !blocked (.send x p)

private theorem MoveLabel.Realizes.allowed_iff {blocked : CommunicationAction schema → Bool}
    {L : Set (CommunicationAction schema)} (hc : ∀ c, blocked c = true ↔ c ∈ L)
    {l pt hl a pt' hl'} (hr : MoveLabel.Realizes l pt hl a pt' hl') :
    l.allowed blocked = true ↔ actionAllowed L a := by
  cases hr <;> simp [MoveLabel.allowed, actionAllowed, ← hc]

/-- Filter an already completed row and reapply the same restriction to each
retained residual. In particular, a synchronization is already a visible
reconfiguration at this stage. -/
def restrictMoves (L : Set (CommunicationAction schema)) (blocked : CommunicationAction schema → Bool)
    (row : List (SymbolicMove schema)) : List (SymbolicMove schema) :=
  (row.filter fun move => move.1.allowed blocked).map fun (l, q) => (l, .restrict L q)

private theorem mem_restrictMoves {L : Set (CommunicationAction schema)} {blocked row l q} :
    (l, q) ∈ restrictMoves L blocked row ↔
      ∃ u, (l, u) ∈ row ∧ l.allowed blocked = true ∧ q = .restrict L u := by
  simp only [restrictMoves, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨k, u⟩, ⟨hm, ha⟩, he⟩
    cases he
    exact ⟨u, hm, ha, rfl⟩
  · rintro ⟨u, hm, ha, rfl⟩
    exact ⟨(l, u), ⟨hm, ha⟩, rfl⟩

theorem MovesExact.restrict {G p row} (he : MovesExact G p row)
    {L : Set (CommunicationAction schema)} {blocked : CommunicationAction schema → Bool}
    (hc : ∀ c, blocked c = true ↔ c ∈ L) :
    MovesExact G (.restrict L p) (restrictMoves L blocked row) := by
  intro pt hl a q pt' hl'
  constructor
  · intro hs
    cases hs with
    | restrict _ _ u _ _ _ _ _ ha hs =>
        obtain ⟨l, hm, hr⟩ := (he ..).mp hs
        exact ⟨l, mem_restrictMoves.mpr ⟨u, hm, (hr.allowed_iff hc).mpr ha, rfl⟩, hr⟩
  · rintro ⟨l, hm, hr⟩
    obtain ⟨u, hu, ha, rfl⟩ := mem_restrictMoves.mp hm
    exact .restrict L p u a pt pt' hl hl' ((hr.allowed_iff hc).mp ha)
      ((he ..).mpr ⟨l, hu, hr⟩)

/-- Compute one symbolic step structurally. References consult a table of
    already checked rows. Prefix continuations are carried as targets. -/
def localMoves (resolve : NodeId → Option (List (SymbolicMove schema))) :
    (p : GProc schema) → (checks : Option (RestrictionChecks schema) := none) → Option (List (SymbolicMove schema))
  | .deadlock, _ => some []
  | .nSeq p q, _ => some [(.visible (.packet p), q)]
  | .rcfgPrefix x p q, _ => some [(.visible (.rcfg x p), q)]
  | .recv x p q, _ => some [(.recv x p, q)]
  | .send x p q, _ => some [(.send x p, q)]
  | .ref i, _ => resolve i
  | .choice p q, checks => do
      let left ← localMoves resolve p (checks.map (RestrictionChecks.child false))
      let right ← localMoves resolve q (checks.map (RestrictionChecks.child true))
      return left ++ right
  | .parallel p q, checks => do
      let left ← localMoves resolve p (checks.map (RestrictionChecks.child false))
      let right ← localMoves resolve q (checks.map (RestrictionChecks.child true))
      return leftMoves q left ++ rightMoves p right ++ syncMoves left right
  | .leftMerge p q, checks =>
      (localMoves resolve p (checks.map (RestrictionChecks.child false))).map (leftMoves q)
  | .commMerge p q, checks => do
      let left ← localMoves resolve p (checks.map (RestrictionChecks.child false))
      let right ← localMoves resolve q (checks.map (RestrictionChecks.child true))
      return syncMoves left right
  | .project 0 _, _ => some []
  | .project (n + 1) p, checks =>
      (localMoves resolve p (checks.map (RestrictionChecks.child false))).map (projectedMoves n)
  | .restrict L p, some check =>
      (localMoves resolve p (some (RestrictionChecks.child false check))).map (restrictMoves L (check []))
  | .restrict _ _, none => none

/-- Correctness of the supplied classifiers at the active restriction sites.
A scan with no classifiers rejects a restriction before visiting its child. -/
def RestrictionChecksCorrect (atRef : NodeId → Prop) :
    (GProc schema) → Option (RestrictionChecks schema) → Prop
  | .ref i, _ => atRef i
  | .restrict L p, some check =>
      (∀ c, check [] c = true ↔ c ∈ L) ∧
        RestrictionChecksCorrect atRef p (some (RestrictionChecks.child false check))
  | .choice p q, checks | .parallel p q, checks | .commMerge p q, checks =>
      RestrictionChecksCorrect atRef p (checks.map (RestrictionChecks.child false)) ∧
        RestrictionChecksCorrect atRef q (checks.map (RestrictionChecks.child true))
  | .leftMerge p _, checks | .project (_ + 1) p, checks =>
      RestrictionChecksCorrect atRef p (checks.map (RestrictionChecks.child false))
  | _, _ => True

theorem RestrictionChecksCorrect.none (p : GProc schema) :
    RestrictionChecksCorrect (fun _ => True) p none := by
  induction p with
  | project n p ih => cases n <;> simp_all [RestrictionChecksCorrect]
  | _ => simp_all [RestrictionChecksCorrect]

/-- The structural domain of one-step row computation. Prefixes carry
    their continuation as data. A left merge inspects its left operand,
    and a zero projection inspects neither transitions nor references. -/
def MoveAdmissible (known : NodeId → Prop) (p : GProc schema) (allowRestriction : Bool := false) :
    Prop :=
  match p with
  | .ref i => known i
  | .restrict _ p => allowRestriction = true ∧ MoveAdmissible known p allowRestriction
  | .choice p q | .parallel p q | .commMerge p q =>
      MoveAdmissible known p allowRestriction ∧ MoveAdmissible known q allowRestriction
  | .leftMerge p _ | .project (_ + 1) p => MoveAdmissible known p allowRestriction
  | _ => True

theorem MoveAdmissible.congr {known other : NodeId → Prop} (h : ∀ i, known i ↔ other i)
    (p : GProc schema) (allowRestriction : Bool := false) :
    MoveAdmissible known p allowRestriction ↔ MoveAdmissible other p allowRestriction := by
  induction p with
  | project n p ih => cases n <;> simp [MoveAdmissible, ih]
  | ref i => exact h i
  | _ => simp_all [MoveAdmissible]

private theorem childChecks_isSome (right : Bool) (checks : Option (RestrictionChecks schema)) :
    (checks.map (RestrictionChecks.child right)).isSome = checks.isSome := by
  cases checks <;> rfl

theorem localMoves_exists_iff_with (resolve : NodeId → Option (List (SymbolicMove schema)))
    (p : GProc schema) (checks : Option (RestrictionChecks schema)) :
    (∃ row, localMoves resolve p checks = some row) ↔
      MoveAdmissible (fun i => ∃ row, resolve i = some row) p checks.isSome := by
  induction p generalizing checks with
  | choice p q ihp ihq | parallel p q ihp ihq | commMerge p q ihp ihq =>
      have hp' := ihp (checks.map (RestrictionChecks.child false))
      have hq' := ihq (checks.map (RestrictionChecks.child true))
      simp only [childChecks_isSome] at hp' hq'
      rw [MoveAdmissible, ← hp', ← hq']
      cases hp : localMoves resolve p (checks.map (RestrictionChecks.child false)) <;>
        cases hq : localMoves resolve q (checks.map (RestrictionChecks.child true)) <;>
        simp [localMoves, hp, hq]
  | leftMerge p q ihp _ =>
      have hp' := ihp (checks.map (RestrictionChecks.child false))
      simp only [childChecks_isSome] at hp'
      rw [MoveAdmissible, ← hp']
      cases hp : localMoves resolve p (checks.map (RestrictionChecks.child false)) <;> simp [localMoves, hp]
  | project n p ih =>
      cases n with
      | zero => simp [localMoves, MoveAdmissible]
      | succ n =>
          have hp' := ih (checks.map (RestrictionChecks.child false))
          simp only [childChecks_isSome] at hp'
          rw [MoveAdmissible, ← hp']
          cases hp : localMoves resolve p (checks.map (RestrictionChecks.child false)) <;> simp [localMoves, hp]
  | restrict L p ih =>
      cases checks with
      | none => simp [localMoves, MoveAdmissible]
      | some check =>
          have hh := ih (some (RestrictionChecks.child false check))
          cases hp : localMoves resolve p (some (RestrictionChecks.child false check)) <;>
            simp_all [localMoves, MoveAdmissible]
  | _ => simp [localMoves, MoveAdmissible]

theorem localMoves_exists_iff (resolve : NodeId → Option (List (SymbolicMove schema))) (p : GProc schema) :
    (∃ row, localMoves resolve p = some row) ↔
      MoveAdmissible (fun i => ∃ row, resolve i = some row) p :=
  localMoves_exists_iff_with resolve p none

private theorem exact_deadlock (G : ProcessGraph schema) : MovesExact G .deadlock [] := by
  intro pt hl a q pt' hl'
  simp only [List.not_mem_nil, false_and, exists_false, iff_false]
  intro h
  cases h

private theorem exact_packet (G : ProcessGraph schema) (p : NetKAT schema) (q : GProc schema) :
    MovesExact G (.nSeq p q) [(.visible (.packet p), q)] := by
  intro pt hl a u pt' hl'
  constructor
  · intro h
    cases h with
    | seq_ok _ _ _ _ _ _ h => exact ⟨_, by simp, .packet h⟩
  · rintro ⟨l, hm, h⟩
    cases List.mem_singleton.mp hm
    cases h with
    | packet h => exact .seq_ok _ _ _ _ _ _ h

private theorem exact_rcfg (G : ProcessGraph schema) (x : Channel) (p : NetKAT schema) (q : GProc schema) :
    MovesExact G (.rcfgPrefix x p q) [(.visible (.rcfg x p), q)] := by
  intro pt hl a u pt' hl'
  constructor
  · intro h
    cases h
    exact ⟨_, by simp, .rcfg⟩
  · rintro ⟨l, hm, h⟩
    cases List.mem_singleton.mp hm
    cases h
    exact .rcfg _ _ _ _ _

private theorem exact_recv (G : ProcessGraph schema) (x : Channel) (p : NetKAT schema) (q : GProc schema) :
    MovesExact G (.recv x p q) [(.recv x p, q)] := by
  intro pt hl a u pt' hl'
  constructor
  · intro h
    cases h
    exact ⟨_, by simp, .recv⟩
  · rintro ⟨l, hm, h⟩
    cases List.mem_singleton.mp hm
    cases h
    exact .recv _ _ _ _ _

private theorem exact_send (G : ProcessGraph schema) (x : Channel) (p : NetKAT schema) (q : GProc schema) :
    MovesExact G (.send x p q) [(.send x p, q)] := by
  intro pt hl a u pt' hl'
  constructor
  · intro h
    cases h
    exact ⟨_, by simp, .send⟩
  · rintro ⟨l, hm, h⟩
    cases List.mem_singleton.mp hm
    cases h
    exact .send _ _ _ _ _

private theorem exact_choice {G : ProcessGraph schema} {p q : GProc schema} {L M}
    (hp : MovesExact G p L) (hq : MovesExact G q M) :
    MovesExact G (.choice p q) (L ++ M) := by
  intro pt hl a u pt' hl'
  constructor
  · intro h
    cases h with
    | choice_l _ _ _ _ _ _ _ _ step =>
        obtain ⟨l, hm, hr⟩ := (hp ..).mp step
        exact ⟨l, List.mem_append_left _ hm, hr⟩
    | choice_r _ _ _ _ _ _ _ _ step =>
        obtain ⟨l, hm, hr⟩ := (hq ..).mp step
        exact ⟨l, List.mem_append_right _ hm, hr⟩
  · rintro ⟨l, hm, hr⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact .choice_l _ _ _ _ _ _ _ _ ((hp ..).mpr ⟨l, hm, hr⟩)
    · exact .choice_r _ _ _ _ _ _ _ _ ((hq ..).mpr ⟨l, hm, hr⟩)

private theorem syncRow_forward {G : ProcessGraph schema} {p q u v : GProc schema} {L M}
    {pt hl : List schema.Packet} {x : Channel} {N : NetKAT schema}
    (hp : MovesExact G p L) (hq : MovesExact G q M)
    (h : (GStep G ⟨p, pt, hl⟩ (.send x N) ⟨u, pt, hl⟩ ∧
            GStep G ⟨q, pt, hl⟩ (.recv x N) ⟨v, pt, hl⟩) ∨
         (GStep G ⟨p, pt, hl⟩ (.recv x N) ⟨u, pt, hl⟩ ∧
            GStep G ⟨q, pt, hl⟩ (.send x N) ⟨v, pt, hl⟩)) :
    (.visible (.rcfg x N), .parallel u v) ∈ syncMoves L M := by
  apply mem_syncMoves.mpr
  refine ⟨x, N, u, v, rfl, rfl, ?_⟩
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain ⟨_, hm₁, hr₁⟩ := (hp ..).mp h₁
    obtain ⟨_, hm₂, hr₂⟩ := (hq ..).mp h₂
    cases hr₁
    cases hr₂
    exact Or.inl ⟨hm₁, hm₂⟩
  · obtain ⟨_, hm₁, hr₁⟩ := (hp ..).mp h₁
    obtain ⟨_, hm₂, hr₂⟩ := (hq ..).mp h₂
    cases hr₁
    cases hr₂
    exact Or.inr ⟨hm₁, hm₂⟩

private theorem syncRow_backward {G : ProcessGraph schema} {p q w : GProc schema} {L M}
    {pt hl pt' hl' : List schema.Packet} {a : Action schema} {l : MoveLabel schema}
    (hp : MovesExact G p L) (hq : MovesExact G q M)
    (hm : (l, w) ∈ syncMoves L M) (hr : MoveLabel.Realizes l pt hl a pt' hl') :
    (GStep G ⟨.parallel p q, pt, hl⟩ a ⟨w, pt', hl'⟩ ∧
     GStep G ⟨.commMerge p q, pt, hl⟩ a ⟨w, pt', hl'⟩) := by
  obtain ⟨x, N, u, v, rfl, rfl, h⟩ := mem_syncMoves.mp hm
  cases hr
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have hs := (hp pt hl (.send x N) u pt hl).mpr ⟨_, h₁, .send⟩
    have hv := (hq pt hl (.recv x N) v pt hl).mpr ⟨_, h₂, .recv⟩
    exact ⟨.sync_send_recv _ _ _ _ _ _ _ _ hs hv, .comm_merge_send_recv _ _ _ _ _ _ _ _ hs hv⟩
  · have hs := (hp pt hl (.recv x N) u pt hl).mpr ⟨_, h₁, .recv⟩
    have hv := (hq pt hl (.send x N) v pt hl).mpr ⟨_, h₂, .send⟩
    exact ⟨.sync_recv_send _ _ _ _ _ _ _ _ hs hv, .comm_merge_recv_send _ _ _ _ _ _ _ _ hs hv⟩

private theorem exact_parallel {G : ProcessGraph schema} {p q : GProc schema} {L M}
    (hp : MovesExact G p L) (hq : MovesExact G q M) :
    MovesExact G (.parallel p q) (leftMoves q L ++ rightMoves p M ++ syncMoves L M) := by
  intro pt hl a w pt' hl'
  constructor
  · intro h
    cases h with
    | par_l _ _ _ _ _ _ _ _ step =>
        obtain ⟨l, hm, hr⟩ := (hp ..).mp step
        exact ⟨l, List.mem_append_left _ (List.mem_append_left _ (mem_leftMoves.mpr ⟨_, hm, rfl⟩)), hr⟩
    | par_r _ _ _ _ _ _ _ _ step =>
        obtain ⟨l, hm, hr⟩ := (hq ..).mp step
        exact ⟨l, List.mem_append_left _ (List.mem_append_right _ (mem_rightMoves.mpr ⟨_, hm, rfl⟩)), hr⟩
    | sync_recv_send _ _ _ _ _ _ _ _ h₁ h₂ =>
        exact ⟨_, List.mem_append_right _ (syncRow_forward hp hq (Or.inr ⟨h₁, h₂⟩)), .rcfg⟩
    | sync_send_recv _ _ _ _ _ _ _ _ h₁ h₂ =>
        exact ⟨_, List.mem_append_right _ (syncRow_forward hp hq (Or.inl ⟨h₁, h₂⟩)), .rcfg⟩
  · rintro ⟨l, hm, hr⟩
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨u, hu, rfl⟩ := mem_leftMoves.mp hm
        exact .par_l _ _ _ _ _ _ _ _ ((hp ..).mpr ⟨l, hu, hr⟩)
      · obtain ⟨v, hv, rfl⟩ := mem_rightMoves.mp hm
        exact .par_r _ _ _ _ _ _ _ _ ((hq ..).mpr ⟨l, hv, hr⟩)
    · exact (syncRow_backward hp hq hm hr).1

private theorem exact_leftMerge {G : ProcessGraph schema} {p q : GProc schema} {L}
    (hp : MovesExact G p L) : MovesExact G (.leftMerge p q) (leftMoves q L) := by
  intro pt hl a w pt' hl'
  constructor
  · intro h
    cases h with
    | left_merge _ _ _ _ _ _ _ _ step =>
        obtain ⟨l, hm, hr⟩ := (hp ..).mp step
        exact ⟨l, mem_leftMoves.mpr ⟨_, hm, rfl⟩, hr⟩
  · rintro ⟨l, hm, hr⟩
    obtain ⟨u, hu, rfl⟩ := mem_leftMoves.mp hm
    exact .left_merge _ _ _ _ _ _ _ _ ((hp ..).mpr ⟨l, hu, hr⟩)

private theorem exact_commMerge {G : ProcessGraph schema} {p q : GProc schema} {L M}
    (hp : MovesExact G p L) (hq : MovesExact G q M) :
    MovesExact G (.commMerge p q) (syncMoves L M) := by
  intro pt hl a w pt' hl'
  constructor
  · intro h
    cases h with
    | comm_merge_recv_send _ _ _ _ _ _ _ _ h₁ h₂ =>
        exact ⟨_, syncRow_forward hp hq (Or.inr ⟨h₁, h₂⟩), .rcfg⟩
    | comm_merge_send_recv _ _ _ _ _ _ _ _ h₁ h₂ =>
        exact ⟨_, syncRow_forward hp hq (Or.inl ⟨h₁, h₂⟩), .rcfg⟩
  · rintro ⟨l, hm, hr⟩
    exact (syncRow_backward hp hq hm hr).2

private theorem exact_project {G : ProcessGraph schema} {p : GProc schema} {n : Nat} {L}
    (hp : MovesExact G p L) : MovesExact G (.project (n + 1) p) (projectedMoves n L) := by
  intro pt hl a w pt' hl'
  constructor
  · intro h
    cases h with
    | project _ _ _ _ _ _ _ _ step =>
        obtain ⟨l, hm, hr⟩ := (hp ..).mp step
        exact ⟨l, mem_projectedMoves.mpr ⟨_, hm, rfl⟩, hr⟩
  · rintro ⟨l, hm, hr⟩
    obtain ⟨u, hu, rfl⟩ := mem_projectedMoves.mp hm
    exact .project _ _ _ _ _ _ _ _ ((hp ..).mpr ⟨l, hu, hr⟩)

/-- A successful structural computation denotes exactly the SOS steps,
    provided that every row returned by the reference lookup is exact. -/
theorem localMoves_exact_with {G : ProcessGraph schema} {resolve : NodeId → Option (List (SymbolicMove schema))}
    {atRef : NodeId → Prop}
    (href : ∀ i, atRef i → ∀ row, resolve i = some row → MovesExact G (.ref i) row)
    {p : GProc schema} {row : List (SymbolicMove schema)} {checks : Option (RestrictionChecks schema)}
    (hc : RestrictionChecksCorrect atRef p checks) (h : localMoves resolve p checks = some row) :
    MovesExact G p row := by
  induction p generalizing row checks with
  | deadlock => cases h; exact exact_deadlock G
  | nSeq p q => cases h; exact exact_packet G p q
  | rcfgPrefix x p q => cases h; exact exact_rcfg G x p q
  | recv x p q => cases h; exact exact_recv G x p q
  | send x p q => cases h; exact exact_send G x p q
  | ref i => exact href i hc row h
  | restrict L p ih =>
      cases checks with
      | none => cases h
      | some check =>
          obtain ⟨bodyRow, hBody, rfl⟩ := Option.map_eq_some'.mp h
          exact (ih hc.2 hBody).restrict hc.1
  | choice p q ihp ihq | parallel p q ihp ihq | commMerge p q ihp ihq =>
      obtain ⟨L, hL, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨M, hM, he⟩ := Option.bind_eq_some_iff.mp h
      cases he
      first
      | exact exact_choice (ihp hc.1 hL) (ihq hc.2 hM)
      | exact exact_parallel (ihp hc.1 hL) (ihq hc.2 hM)
      | exact exact_commMerge (ihp hc.1 hL) (ihq hc.2 hM)
  | leftMerge p q ihp _ =>
      obtain ⟨L, hL, rfl⟩ := Option.map_eq_some'.mp h
      exact exact_leftMerge (ihp hc hL)
  | project n p ih =>
      cases n with
      | zero =>
          cases h
          intro pt hl a q pt' hl'
          simp only [List.not_mem_nil, false_and, exists_false, iff_false]
          intro h
          cases h
      | succ n =>
          obtain ⟨L, hL, rfl⟩ := Option.map_eq_some'.mp h
          exact exact_project (ih hc hL)

theorem localMoves_exact {G : ProcessGraph schema} {resolve : NodeId → Option (List (SymbolicMove schema))}
    (href : ∀ i row, resolve i = some row → MovesExact G (.ref i) row)
    {p : GProc schema} {row : List (SymbolicMove schema)} (h : localMoves resolve p = some row) :
    MovesExact G p row :=
  localMoves_exact_with (fun i _ => href i) (.none p) h

/-- Lookup preserves the same single step, including its action and both lists. -/
theorem MovesExact.ref {G : ProcessGraph schema} {i : NodeId} {row}
    (h : MovesExact G (G.label i) row) : MovesExact G (.ref i) row := by
  intro pt hl a q pt' hl'
  exact (⟨gstep_ref_inv, fun hs => .var _ _ _ _ _ _ _ hs⟩ :
    GStep G ⟨.ref i, pt, hl⟩ a ⟨q, pt', hl'⟩ ↔ GStep G ⟨G.label i, pt, hl⟩ a ⟨q, pt', hl'⟩).trans
    (h ..)

/-- Resolve references on demand by computing the initial row of their body.
The outer pass descends through the root. The body pass descends through
the body with lookup disabled. Neither pass traverses prefix continuations. -/
def guardedMoves (G : ProcessGraph schema) (p : GProc schema)
    (rootChecks : Option (RestrictionChecks schema) := none)
    (bodyChecks : NodeId → Option (RestrictionChecks schema) := fun _ => none) : Option (List (SymbolicMove schema)) :=
  localMoves (fun i => localMoves (fun _ => none) (G.label i) (bodyChecks i)) p rootChecks

/-- Check the root's active restrictions and those in each body it consults.
A body scan disables references, so it needs no further classifiers. -/
def GuardedRestrictionChecksCorrect (G : ProcessGraph schema) (p : GProc schema)
    (rootChecks : Option (RestrictionChecks schema)) (bodyChecks : NodeId → Option (RestrictionChecks schema)) :
    Prop :=
  RestrictionChecksCorrect
    (fun i => RestrictionChecksCorrect (fun _ => True) (G.label i) (bodyChecks i)) p rootChecks

theorem guardedMoves_exact_with {G : ProcessGraph schema} {p : GProc schema} {row : List (SymbolicMove schema)}
    {rootChecks : Option (RestrictionChecks schema)} {bodyChecks : NodeId → Option (RestrictionChecks schema)}
    (hc : GuardedRestrictionChecksCorrect G p rootChecks bodyChecks)
    (h : guardedMoves G p rootChecks bodyChecks = some row) : MovesExact G p row :=
  localMoves_exact_with
    (fun _ hChecks _ hBody => MovesExact.ref (localMoves_exact_with (by simp) hChecks hBody)) hc h

theorem guardedMoves_exact {G : ProcessGraph schema} {p : GProc schema} {row : List (SymbolicMove schema)}
    (h : guardedMoves G p = some row) : MovesExact G p row :=
  localMoves_exact (fun _ _ hb => MovesExact.ref (localMoves_exact (by simp) hb)) h

theorem guardedMoves_exists_iff (G : ProcessGraph schema) (p : GProc schema) :
    (∃ row, guardedMoves G p = some row) ↔
      MoveAdmissible (fun i => MoveAdmissible (fun _ => False) (G.label i)) p := by
  unfold guardedMoves
  refine (localMoves_exists_iff _ _).trans (MoveAdmissible.congr (fun i => ?_) p)
  simpa using localMoves_exists_iff (fun _ => none) (G.label i)

/-- With classifiers available, a guarded body needs no active lookup. -/
theorem guarded_body_moveAdmissible {p : DyNetKAT schema} (hg : GuardedOccurrences p) :
    MoveAdmissible (fun _ => False) (toGProc p) true := by
  induction p with
  | project n p ih =>
      cases n <;> simp_all [GuardedOccurrences, MoveAdmissible, toGProc]
  | _ => simp_all [GuardedOccurrences, MoveAdmissible, toGProc]

private theorem MoveAdmissible.imp_of_refs {known other : NodeId → Prop} {p : GProc schema}
    (h : MoveAdmissible known p true)
    (hi : ∀ i ∈ gprocRefs p, known i → other i) : MoveAdmissible other p true := by
  induction p with
  | project n p ih =>
      cases n <;> simp_all [MoveAdmissible, gprocRefs]
  | ref i =>
      exact hi i (by simp [gprocRefs]) h
  | _ =>
      simp_all [MoveAdmissible, gprocRefs, Finset.mem_union, or_imp, forall_and]

private theorem MoveAdmissible.of_refs {known : NodeId → Prop} (p : GProc schema)
    (h : ∀ i ∈ gprocRefs p, known i) : MoveAdmissible known p true := by
  induction p with
  | project n p ih => cases n <;> simp_all [MoveAdmissible, gprocRefs]
  | ref i => exact h i (by simp [gprocRefs])
  | _ => simp_all [MoveAdmissible, gprocRefs, Finset.mem_union, or_imp, forall_and]

/-- Finite support and reachable-body guardedness suffice for computation
with classifiers. Correctness of the classifiers is used by exactness. -/
theorem guardedMoves_toGraph_exists {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hsup : FiniteSupport env root S) (hw : WellFormed env root)
    (rootChecks : RestrictionChecks schema) (bodyChecks : NodeId → RestrictionChecks schema) :
    ∃ row, guardedMoves (toGraph env root S hsup) (toGProc root)
      (some rootChecks) (fun i => some (bodyChecks i)) = some row := by
  unfold guardedMoves
  apply (localMoves_exists_iff_with _ _ _).mpr
  apply MoveAdmissible.of_refs
  intro i hi
  rw [gprocRefs_toGProc, Finset.mem_image] at hi
  obtain ⟨x, hx, rfl⟩ := hi
  obtain ⟨body, hb⟩ := WellFormed.reachable_definition env root hw x (.direct hx)
  rw [toGraph_label_varNode hsup (hsup.1 hx), hb, Option.getD_some]
  apply (localMoves_exists_iff_with _ _ _).mpr
  have hg := guarded_body_moveAdmissible
    (WellFormed.reachable_guarded env root hw x body (.direct hx) hb)
  exact hg.imp_of_refs (by simp)

/-- Two-way source SOS correspondence at each fixed action and packet lists. -/
def SourceMovesExact (G : ProcessGraph schema) (env : RecEnv schema) (p : DyNetKAT schema)
    (row : List (SymbolicMove schema)) : Prop :=
  ∀ (pt hl : List schema.Packet) (a : Action schema) (pt' hl' : List schema.Packet),
    (∀ l q, (l, q) ∈ row → MoveLabel.Realizes l pt hl a pt' hl' →
      ∃ p', Step env ⟨p, pt, hl⟩ a ⟨p', pt', hl'⟩ ∧ Corr G env p' q) ∧
    (∀ p', Step env ⟨p, pt, hl⟩ a ⟨p', pt', hl'⟩ →
      ∃ l q, (l, q) ∈ row ∧ MoveLabel.Realizes l pt hl a pt' hl' ∧ Corr G env p' q)

theorem MovesExact.source_steps {G : ProcessGraph schema} {env : RecEnv schema} {p : DyNetKAT schema}
    {gp : GProc schema} {row : List (SymbolicMove schema)} (he : MovesExact G gp row)
    (hc : Corr G env p gp) : SourceMovesExact G env p row := by
  intro pt hl a pt' hl'
  constructor
  · intro l q hm hr
    exact gstep_to_step G env ⟨gp, pt, hl⟩ ⟨q, pt', hl'⟩ a
      ((he ..).mpr ⟨l, hm, hr⟩) p hc
  · intro p' h
    obtain ⟨q, hg, hq⟩ := step_to_gstep G env ⟨p, pt, hl⟩ ⟨p', pt', hl'⟩ a h gp hc
    obtain ⟨l, hm, hr⟩ := (he ..).mp hg
    exact ⟨l, q, hm, hr, hq⟩

/-- The executable one-step oracle for a finitely supported guarded source root.
The only additional input is correct membership at active restriction sites. -/
theorem guardedMoves_toGraph_source_exact {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hsup : FiniteSupport env root S) (hw : WellFormed env root)
    (rootChecks : RestrictionChecks schema) (bodyChecks : NodeId → RestrictionChecks schema)
    (hc : GuardedRestrictionChecksCorrect (toGraph env root S hsup) (toGProc root)
      (some rootChecks) (fun i => some (bodyChecks i))) :
    ∃ row, guardedMoves (toGraph env root S hsup) (toGProc root)
      (some rootChecks) (fun i => some (bodyChecks i)) = some row ∧
      SourceMovesExact (toGraph env root S hsup) env root row := by
  obtain ⟨row, h⟩ := guardedMoves_toGraph_exists hsup hw rootChecks bodyChecks
  exact ⟨row, h, (guardedMoves_exact_with hc h).source_steps (toGraph_corr env root S hsup)⟩

abbrev ReferenceRows (schema : PacketSchema := ctxSchema) := List (NodeId × List (SymbolicMove schema))

def referenceMoves (rows : ReferenceRows schema) (i : NodeId) : Option (List (SymbolicMove schema)) :=
  rows.findSome? fun (j, moves) => if i = j then some moves else none

/-- Check the finite dependency order for resolving reference steps.
    Each label can consult only rows computed earlier in the order. -/
def buildReferenceRows (G : ProcessGraph schema) :
    List NodeId → ReferenceRows schema → Option (ReferenceRows schema)
  | [], rows => some rows
  | i :: rest, rows => do
      let moves ← localMoves (referenceMoves rows) (G.label i)
      buildReferenceRows G rest ((i, moves) :: rows)

theorem buildReferenceRows_exact {G : ProcessGraph schema} {order : List NodeId}
    {input output : ReferenceRows schema}
    (h : buildReferenceRows G order input = some output)
    (hInput : ∀ i row, referenceMoves input i = some row → MovesExact G (.ref i) row) :
    ∀ i row, referenceMoves output i = some row → MovesExact G (.ref i) row := by
  induction order generalizing input with
  | nil => cases h; exact hInput
  | cons i rest ih =>
      obtain ⟨moves, hm, hRest⟩ := Option.bind_eq_some_iff.mp h
      apply ih hRest
      intro j row hj
      by_cases he : j = i
      · subst j
        have heq : moves = row := Option.some.inj (by simpa [referenceMoves] using hj)
        subst row
        exact MovesExact.ref (localMoves_exact hInput hm)
      · exact hInput j row (by simpa [referenceMoves, he] using hj)

theorem referenceMoves_exists_iff (rows : ReferenceRows schema) (i : NodeId) :
    (∃ row, referenceMoves rows i = some row) ↔ i ∈ (rows.map Prod.fst).toFinset := by
  induction rows with
  | nil => simp [referenceMoves]
  | cons entry rows ih =>
      rcases entry with ⟨j, moves⟩
      by_cases he : i = j
      · subst j
        simp [referenceMoves]
      · simpa [referenceMoves, he] using ih

/-- A reference order is valid when each active reference in a label
    already has an earlier row, and no active position is a restriction. -/
def ReferenceOrderAdmissible (G : ProcessGraph schema) : Finset NodeId → List NodeId → Prop
  | _, [] => True
  | known, i :: rest =>
      MoveAdmissible (· ∈ known) (G.label i) ∧ ReferenceOrderAdmissible G (insert i known) rest

theorem buildReferenceRows_exists_iff (G : ProcessGraph schema) (order : List NodeId)
    (input : ReferenceRows schema) :
    (∃ output, buildReferenceRows G order input = some output) ↔
      ReferenceOrderAdmissible G (input.map Prod.fst).toFinset order := by
  induction order generalizing input with
  | nil => simp [buildReferenceRows, ReferenceOrderAdmissible]
  | cons i rest ih =>
      have hLocal := (localMoves_exists_iff (referenceMoves input) (G.label i)).trans
        (MoveAdmissible.congr (referenceMoves_exists_iff input) _)
      cases hm : localMoves (referenceMoves input) (G.label i) with
      | none =>
          simp [hm] at hLocal
          simp only [buildReferenceRows, hm, ReferenceOrderAdmissible, hLocal, false_and]
          change (∃ output : ReferenceRows schema, (none : Option (ReferenceRows schema)) = some output) ↔ False
          simp
      | some moves =>
          have hs := hLocal.mp ⟨moves, hm⟩
          simpa only [buildReferenceRows, hm, Option.some_bind, ReferenceOrderAdmissible, hs,
            true_and, List.map_cons, Prod.fst, List.toFinset_cons] using
            (ih ((i, moves) :: input))

theorem buildReferenceRows_keys {G : ProcessGraph schema} {order : List NodeId}
    {input output : ReferenceRows schema} (h : buildReferenceRows G order input = some output) :
    output.map Prod.fst = order.reverse ++ input.map Prod.fst := by
  induction order generalizing input with
  | nil => cases h; rfl
  | cons i rest ih =>
      obtain ⟨moves, _, hRest⟩ := Option.bind_eq_some_iff.mp h
      rw [ih hRest]
      simp [List.reverse_cons, List.append_assoc]

/-- Classifiers for every restriction in the syntax, including continuations
and passive operands that may become active after a step. -/
def AllRestrictionChecksCorrect : GProc schema → RestrictionChecks schema → Prop
  | .restrict L p, c => (∀ a, c [] a = true ↔ a ∈ L) ∧
      AllRestrictionChecksCorrect p (c.child false)
  | .nSeq _ p, c | .recv _ _ p, c | .send _ _ p, c | .rcfgPrefix _ _ p, c |
    .project _ p, c => AllRestrictionChecksCorrect p (c.child false)
  | .choice p q, c | .parallel p q, c | .leftMerge p q, c | .commMerge p q, c =>
      AllRestrictionChecksCorrect p (c.child false) ∧ AllRestrictionChecksCorrect q (c.child true)
  | _, _ => True

theorem AllRestrictionChecksCorrect.active {p : GProc schema} {c : RestrictionChecks schema}
    {known : NodeId → Prop} (h : AllRestrictionChecksCorrect p c)
    (hr : ∀ i ∈ gprocRefs p, known i) : RestrictionChecksCorrect known p (some c) := by
  induction p generalizing c with
  | project n p ih => cases n <;> simp_all [AllRestrictionChecksCorrect,
      RestrictionChecksCorrect, gprocRefs]
  | ref i => exact hr i (Finset.mem_singleton_self i)
  | _ => simp_all [AllRestrictionChecksCorrect, RestrictionChecksCorrect, gprocRefs,
      Finset.mem_union, forall_and, or_imp]

/-- A graph term with executable classifiers addressed relative to that term. -/
structure CheckedResidual (schema : PacketSchema := ctxSchema) where
  proc : GProc schema
  checks : RestrictionChecks schema

namespace CheckedResidual

def parallel (p q : CheckedResidual schema) : CheckedResidual schema :=
  ⟨.parallel p.proc q.proc, fun
    | false :: rest => p.checks rest
    | true :: rest => q.checks rest
    | [] => fun _ => false⟩

def project (n : Nat) (p : CheckedResidual schema) : CheckedResidual schema :=
  ⟨.project n p.proc, fun path => p.checks path.tail⟩

def restrict (L : Set (CommunicationAction schema)) (blocked : CommunicationAction schema → Bool)
    (p : CheckedResidual schema) : CheckedResidual schema :=
  ⟨.restrict L p.proc, fun
    | [] => blocked
    | _ :: rest => p.checks rest⟩

def Valid (live : NodeId → Prop) (p : CheckedResidual schema) : Prop :=
  (∀ i ∈ gprocRefs p.proc, live i) ∧ AllRestrictionChecksCorrect p.proc p.checks

theorem valid_parallel {live : NodeId → Prop} {p q : CheckedResidual schema}
    (hp : p.Valid live) (hq : q.Valid live) : (p.parallel q).Valid live :=
  ⟨fun i hi => (Finset.mem_union.mp hi).elim (hp.1 i) (hq.1 i), hp.2, hq.2⟩

end CheckedResidual

abbrev CheckedMove (schema : PacketSchema := ctxSchema) := (MoveLabel schema) × (CheckedResidual schema)

def CheckedMove.erase (m : CheckedMove schema) : SymbolicMove schema := (m.1, m.2.proc)

/-- One-step rows with the residual classifiers carried along by the same
prefix, merge, projection, and restriction operations as the graph term. -/
def localCheckedMoves (resolve : NodeId → Option (List (CheckedMove schema))) :
    (GProc schema) → RestrictionChecks schema → Option (List (CheckedMove schema))
  | .deadlock, _ => some []
  | .nSeq N p, c => some [(.visible (.packet N), ⟨p, c.child false⟩)]
  | .rcfgPrefix x N p, c => some [(.visible (.rcfg x N), ⟨p, c.child false⟩)]
  | .recv x N p, c => some [(.recv x N, ⟨p, c.child false⟩)]
  | .send x N p, c => some [(.send x N, ⟨p, c.child false⟩)]
  | .ref i, _ => resolve i
  | .choice p q, c => do
      let l ← localCheckedMoves resolve p (c.child false)
      let r ← localCheckedMoves resolve q (c.child true)
      return l ++ r
  | .parallel p q, c => do
      let l ← localCheckedMoves resolve p (c.child false)
      let r ← localCheckedMoves resolve q (c.child true)
      return l.map (fun (a, t) => (a, t.parallel ⟨q, c.child true⟩)) ++
        r.map (fun (a, t) => (a, (CheckedResidual.mk p (c.child false)).parallel t)) ++
        syncMovesWith CheckedResidual.parallel l r
  | .leftMerge p q, c =>
      (localCheckedMoves resolve p (c.child false)).map
        (List.map fun (a, t) => (a, t.parallel ⟨q, c.child true⟩))
  | .commMerge p q, c => do
      let l ← localCheckedMoves resolve p (c.child false)
      let r ← localCheckedMoves resolve q (c.child true)
      return syncMovesWith CheckedResidual.parallel l r
  | .project 0 _, _ => some []
  | .project (n + 1) p, c =>
      (localCheckedMoves resolve p (c.child false)).map
        (List.map fun (a, t) => (a, t.project n))
  | .restrict L p, c =>
      (localCheckedMoves resolve p (c.child false)).map fun row =>
        (row.filter fun m => m.1.allowed (c [])).map fun (a, t) => (a, t.restrict L (c []))

private theorem erase_syncMove (x y : CheckedMove schema) :
    (syncMoveWith CheckedResidual.parallel x y).map CheckedMove.erase =
      syncMove x.erase y.erase := by
  obtain ⟨x, p⟩ := x
  obtain ⟨y, q⟩ := y
  cases x <;> cases y <;> simp [syncMoveWith, CheckedMove.erase, CheckedResidual.parallel]

private theorem erase_syncMoves (xs ys : List (CheckedMove schema)) :
    (syncMovesWith CheckedResidual.parallel xs ys).map CheckedMove.erase =
      syncMoves (xs.map CheckedMove.erase) (ys.map CheckedMove.erase) := by
  simp only [syncMovesWith, List.map_flatMap, List.flatMap_map]
  congr 1
  funext x
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.map_cons, List.filterMap_cons]
      have h := erase_syncMove x y
      cases he : syncMoveWith CheckedResidual.parallel x y <;>
        simp [he, ← h, ih]

private theorem map_child_some (b : Bool) (c : RestrictionChecks schema) :
    (some c).map (RestrictionChecks.child b) = some (c.child b) := rfl

theorem localCheckedMoves_erase (resolve : NodeId → Option (List (CheckedMove schema)))
    (p : GProc schema) (c : RestrictionChecks schema) :
    (localCheckedMoves resolve p c).map (List.map CheckedMove.erase) =
      localMoves (fun i => (resolve i).map (List.map CheckedMove.erase)) p (some c) := by
  induction p generalizing c with
  | choice p q ihp ihq | parallel p q ihp ihq | commMerge p q ihp ihq =>
      rw [localCheckedMoves, localMoves]
      try simp only [map_child_some]
      rw [← ihp (c.child false), ← ihq (c.child true)]
      cases localCheckedMoves resolve p (c.child false) <;>
        cases localCheckedMoves resolve q (c.child true) <;>
        simp [List.map_append, List.map_map, erase_syncMoves, leftMoves, rightMoves] <;> rfl
  | leftMerge p q ihp _ =>
      rw [localCheckedMoves, localMoves]
      try simp only [map_child_some]
      rw [← ihp (c.child false)]
      cases localCheckedMoves resolve p (c.child false) <;> simp [leftMoves, List.map_map, CheckedMove.erase, CheckedResidual.parallel]
  | project n p ih =>
      cases n with
      | zero => rfl
      | succ n =>
          rw [localCheckedMoves, localMoves]
          try simp only [map_child_some]
          rw [← ih (c.child false)]
          cases localCheckedMoves resolve p (c.child false) <;>
            simp [projectedMoves, List.map_map, CheckedMove.erase, CheckedResidual.project]
  | restrict L p ih =>
      rw [localCheckedMoves, localMoves, ← ih (c.child false)]
      cases localCheckedMoves resolve p (c.child false) <;>
        simp [restrictMoves, List.filter_map, List.map_map] <;> rfl
  | _ => rfl

private theorem valid_syncMoves {live : NodeId → Prop} {xs ys : List (CheckedMove schema)}
    (hx : ∀ m ∈ xs, m.2.Valid live) (hy : ∀ m ∈ ys, m.2.Valid live)
    {m : CheckedMove schema} (hm : m ∈ syncMovesWith CheckedResidual.parallel xs ys) :
    m.2.Valid live := by
  simp only [syncMovesWith, List.mem_flatMap, List.mem_filterMap] at hm
  obtain ⟨⟨a, x⟩, hax, ⟨b, y⟩, hby, he⟩ := hm
  have h := CheckedResidual.valid_parallel (hx _ hax) (hy _ hby)
  cases a <;> cases b <;> simp [syncMoveWith] at he <;> obtain ⟨_, rfl⟩ := he <;> exact h

theorem localCheckedMoves_valid {live : NodeId → Prop} {resolve : NodeId → Option (List (CheckedMove schema))}
    (hr : ∀ i, live i → ∀ row, resolve i = some row → ∀ m ∈ row, m.2.Valid live)
    {p : GProc schema} {c : RestrictionChecks schema} {row : List (CheckedMove schema)}
    (hp : (CheckedResidual.mk p c).Valid live) (he : localCheckedMoves resolve p c = some row) :
    ∀ m ∈ row, m.2.Valid live := by
  induction p generalizing c row with
  | ref i => exact hr i (hp.1 i (Finset.mem_singleton_self i)) row he
  | deadlock => cases he; simp
  | nSeq | send | recv | rcfgPrefix =>
      cases he
      intro m hm
      obtain rfl := List.mem_singleton.mp hm
      exact ⟨hp.1, hp.2⟩
  | choice p q ihp ihq | parallel p q ihp ihq | commMerge p q ihp ihq =>
      have hLeft : (CheckedResidual.mk p (c.child false)).Valid live := ⟨(fun i hi => hp.1 i (Finset.mem_union_left _ hi)), hp.2.1⟩
      have hRight : (CheckedResidual.mk q (c.child true)).Valid live := ⟨(fun i hi => hp.1 i (Finset.mem_union_right _ hi)), hp.2.2⟩
      obtain ⟨L, hL, hRest⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨R, hR, hRow⟩ := Option.bind_eq_some_iff.mp hRest
      cases hRow
      have hLeftRow := ihp hLeft hL
      have hRightRow := ihq hRight hR
      intro m hm
      first
      | rcases List.mem_append.mp hm with hl | hr
        · exact hLeftRow m hl
        · exact hRightRow m hr
      | exact valid_syncMoves hLeftRow hRightRow hm
      | rcases List.mem_append.mp hm with hInterleave | hSync
        · rcases List.mem_append.mp hInterleave with h | h
          · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
            exact CheckedResidual.valid_parallel (hLeftRow k hk) hRight
          · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
            exact CheckedResidual.valid_parallel hLeft (hRightRow k hk)
        · exact valid_syncMoves hLeftRow hRightRow hSync
  | leftMerge p q ihp _ =>
      obtain ⟨L, hL, rfl⟩ := Option.map_eq_some'.mp he
      intro m hm
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
      exact CheckedResidual.valid_parallel (ihp ⟨(fun i hi => hp.1 i (Finset.mem_union_left _ hi)), hp.2.1⟩ hL k hk) ⟨(fun i hi => hp.1 i (Finset.mem_union_right _ hi)), hp.2.2⟩
  | project n p ih =>
      cases n with
      | zero => cases he; simp
      | succ n =>
          obtain ⟨L, hL, rfl⟩ := Option.map_eq_some'.mp he
          intro m hm
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
          have hv := ih ⟨hp.1, hp.2⟩ hL k hk
          exact ⟨hv.1, hv.2⟩
  | restrict L p ih =>
      obtain ⟨R, hR, rfl⟩ := Option.map_eq_some'.mp he
      intro m hm
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
      have hv := ih ⟨hp.1, hp.2.2⟩ hR k (List.mem_filter.mp hk).1
      exact ⟨hv.1, hp.2.1, hv.2⟩

/-- The fixed definition table covers the original root's reachable names.
All later residuals use this same table. -/
structure ProjectionSupport {schema : PacketSchema} (G : ProcessGraph schema) (bodyChecks : NodeId → RestrictionChecks schema)
    (live : NodeId → Prop) : Prop where
  closed : ∀ i, live i → ∀ j ∈ gprocRefs (G.label i), live j
  body : ∀ i, live i → MoveAdmissible (fun _ => False) (G.label i) true ∧
    AllRestrictionChecksCorrect (G.label i) (bodyChecks i)

def checkedMoves (G : ProcessGraph schema) (bodyChecks : NodeId → RestrictionChecks schema)
    (p : CheckedResidual schema) : Option (List (CheckedMove schema)) :=
  localCheckedMoves (fun i => localCheckedMoves (fun _ => none) (G.label i) (bodyChecks i))
    p.proc p.checks

theorem checkedMoves_erase (G : ProcessGraph schema) (bodyChecks : NodeId → RestrictionChecks schema)
    (p : CheckedResidual schema) :
    (checkedMoves G bodyChecks p).map (List.map CheckedMove.erase) =
      guardedMoves G p.proc (some p.checks) (fun i => some (bodyChecks i)) := by
  unfold checkedMoves guardedMoves
  rw [localCheckedMoves_erase]
  congr 1
  funext i
  exact localCheckedMoves_erase (fun _ => none) _ _

theorem checkedMoves_exists {G : ProcessGraph schema} {bodyChecks : NodeId → RestrictionChecks schema}
    {live : NodeId → Prop} (hG : ProjectionSupport G bodyChecks live) {p : CheckedResidual schema} (hp : p.Valid live) :
    ∃ row, checkedMoves G bodyChecks p = some row := by
  have hh : ∃ row, guardedMoves G p.proc (some p.checks) (fun i => some (bodyChecks i)) =
      some row := by
    unfold guardedMoves
    apply (localMoves_exists_iff_with _ _ _).mpr
    apply MoveAdmissible.of_refs
    intro i hi
    apply (localMoves_exists_iff_with _ _ _).mpr
    exact ((hG.body i (hp.1 i hi)).1).imp_of_refs (by simp)
  rw [← checkedMoves_erase] at hh
  obtain ⟨_, h⟩ := hh
  obtain ⟨row, he, _⟩ := Option.map_eq_some'.mp h
  exact ⟨row, he⟩

theorem checkedMoves_spec {G : ProcessGraph schema} {bodyChecks : NodeId → RestrictionChecks schema}
    {live : NodeId → Prop} (hG : ProjectionSupport G bodyChecks live) {p : CheckedResidual schema} (hp : p.Valid live)
    {row : List (CheckedMove schema)} (h : checkedMoves G bodyChecks p = some row) :
    MovesExact G p.proc (row.map CheckedMove.erase) ∧ ∀ m ∈ row, m.2.Valid live := by
  constructor
  · apply guardedMoves_exact_with
    · exact hp.2.active (fun i hi => (hG.body i (hp.1 i hi)).2.active (by simp))
    · simpa [h] using (checkedMoves_erase G bodyChecks p).symm
  · apply localCheckedMoves_valid _ hp h
    intro i hi bodyRow hBody
    exact localCheckedMoves_valid (by simp) ⟨hG.closed i hi, (hG.body i hi).2⟩ hBody

end DyNetKAT.DyNetKAT
