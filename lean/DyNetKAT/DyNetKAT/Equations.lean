import DyNetKAT.DyNetKAT.FiniteProjection
import DyNetKAT.DyNetKAT.NetKATBridge
import DyNetKAT.NetKAT.Normalization

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : PacketSchema}

open DyNetKAT.NetKAT

namespace Equations

private theorem bisimilar_of_matches {schema : PacketSchema} (env : RecEnv schema) (p q : DyNetKAT schema)
    (forward : ∀ pt hl a r pt' hl', Step env ⟨p, pt, hl⟩ a ⟨r, pt', hl'⟩ →
      ∃ s, Step env ⟨q, pt, hl⟩ a ⟨s, pt', hl'⟩ ∧ Bisimilar env r s)
    (backward : ∀ pt hl a s pt' hl', Step env ⟨q, pt, hl⟩ a ⟨s, pt', hl'⟩ →
      ∃ r, Step env ⟨p, pt, hl⟩ a ⟨r, pt', hl'⟩ ∧ Bisimilar env s r) :
    Bisimilar env p q := by
  let R (x y : DyNetKAT schema) := (x = p ∧ y = q) ∨ (x = q ∧ y = p) ∨ Bisimilar env x y
  refine ⟨R, ⟨?_, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
  · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (h.symm env))
  · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨S, hS, hxy⟩) pt hl a r pt' hl' hs
    · obtain ⟨s, hs', h⟩ := forward pt hl a r pt' hl' hs
      exact ⟨s, hs', Or.inr (Or.inr h)⟩
    · obtain ⟨s, hs', h⟩ := backward pt hl a r pt' hl' hs
      exact ⟨s, hs', Or.inr (Or.inr h)⟩
    · obtain ⟨s, hs', h⟩ := hS.2 _ _ hxy pt hl a r pt' hl' hs
      exact ⟨s, hs', Or.inr (Or.inr ⟨S, hS, h⟩)⟩

private theorem bisimilar_of_step_iff {schema : PacketSchema} (env : RecEnv schema) (p q : DyNetKAT schema)
    (h : ∀ pt hl a r pt' hl', Step env ⟨p, pt, hl⟩ a ⟨r, pt', hl'⟩ ↔
      Step env ⟨q, pt, hl⟩ a ⟨r, pt', hl'⟩) : Bisimilar env p q :=
  bisimilar_of_matches env p q
    (fun _ _ _ r _ _ hs => ⟨r, (h ..).mp hs, Bisimilar.refl env r⟩)
    (fun _ _ _ r _ _ hs => ⟨r, (h ..).mpr hs, Bisimilar.refl env r⟩)

private theorem choice_step_iff {env : RecEnv schema} {p q r : DyNetKAT schema}
    {pt hl pt' hl' : List schema.Packet} {a : Action schema} :
    Step env ⟨.choice p q, pt, hl⟩ a ⟨r, pt', hl'⟩ ↔
      Step env ⟨p, pt, hl⟩ a ⟨r, pt', hl'⟩ ∨ Step env ⟨q, pt, hl⟩ a ⟨r, pt', hl'⟩ :=
  ⟨fun hs => choice_step_inv _ _ _ _ _ _ _ _ _ hs, fun h => h.elim
    (Step.cpol_choice_l _ _ _ _ _ _ _ _) (Step.cpol_choice_r _ _ _ _ _ _ _ _)⟩

theorem a0_sound (env : RecEnv schema) (p : DyNetKAT schema) :
    Bisimilar env (.nSeq .drop p) .deadlock := by
  apply bisimilar_of_no_steps
  · intro pt hl a d hs
    cases hs with
    | cpol_seq_ok _ _ _ _ _ _ he => exact he
  · exact deadlock_no_step env

theorem a1_sound (env : RecEnv schema) (z y : NetKAT schema) (p : DyNetKAT schema) :
    Bisimilar env (.nSeq (.union z y) p) (.choice (.nSeq z p) (.nSeq y p)) := by
  apply bisimilar_of_step_iff
  intro pt hl a r pt' hl'
  rw [choice_step_iff]
  constructor
  · intro hs
    cases hs with
    | cpol_seq_ok _ _ _ _ _ _ he =>
      exact (historySem_union ..).mp he |>.imp
        (Step.cpol_seq_ok _ _ _ _ _ _) (Step.cpol_seq_ok _ _ _ _ _ _)
  · rintro (hs | hs) <;> cases hs
    · exact .cpol_seq_ok _ _ _ _ _ _ (Or.inl (by assumption))
    · exact .cpol_seq_ok _ _ _ _ _ _ (Or.inr (by assumption))

/-- Equal NetKAT history relations give identical prefix steps into the shared continuation. -/
theorem nSeq_bisimilar_of_historySemantics {schema : PacketSchema} (env : RecEnv schema) {p q : NetKAT schema} (d : DyNetKAT schema)
    (h : ∀ input output, HistorySemantics p input output ↔ HistorySemantics q input output) :
    Bisimilar env (.nSeq p d) (.nSeq q d) := by
  apply bisimilar_of_step_iff
  intro pt hl a r pt' hl'
  constructor <;> intro hs <;> cases hs
  · exact .cpol_seq_ok _ _ _ _ _ _ ((h ..).mp (by assumption))
  · exact .cpol_seq_ok _ _ _ _ _ _ ((h ..).mpr (by assumption))

/-- Matching singleton packet observations determine the full dup-free history relation. -/
theorem historySemantics_of_nSeq_bisimilar {schema : PacketSchema} {env : RecEnv schema} {p q : NetKAT schema} {d : DyNetKAT schema}
    (h : Bisimilar env (.nSeq p d) (.nSeq q d)) :
    ∀ input output, HistorySemantics p input output ↔ HistorySemantics q input output := by
  have transfer {x y : NetKAT schema} (bisim : Bisimilar env (.nSeq x d) (.nSeq y d))
      (σ τ : schema.Packet) (obs : Semantics x σ τ) : Semantics y σ τ := by
    obtain ⟨R, matching, related⟩ := bisim
    have step := Step.cpol_seq_ok (env := env) x d σ τ [] []
      ((historySemantics_singleton_iff_packetSemantics x σ τ).mpr obs)
    obtain ⟨target, matched, _⟩ := matching.2 _ _ related [σ] [] (.packet σ τ) d [] [τ] step
    obtain ⟨input, output, actionEq, _, evaluates, _⟩ :=
      nSeq_step_inv env y d [σ] [] (.packet σ τ) target [] [τ] matched
    obtain ⟨rfl, rfl⟩ := Action.packet.inj actionEq
    exact (historySemantics_singleton_iff_packetSemantics y σ τ).mp evaluates
  rintro ⟨σ, tail⟩ ⟨τ, tail'⟩
  rw [historySemantics_iff_packetSemantics, historySemantics_iff_packetSemantics]
  exact and_congr_right fun _ => ⟨transfer h σ τ, transfer (h.symm env) σ τ⟩

/-- Semantic layering (arXiv v4 Proposition 1) for dup-free NetKAT over a finite packet schema. -/
theorem historySemantics_iff_nSeq_bisimilar {schema : PacketSchema} (env : RecEnv schema) (p q : NetKAT schema) (d : DyNetKAT schema) :
    (∀ input output, HistorySemantics p input output ↔ HistorySemantics q input output) ↔
      Bisimilar env (.nSeq p d) (.nSeq q d) :=
  ⟨nSeq_bisimilar_of_historySemantics env d, historySemantics_of_nSeq_bisimilar⟩

theorem netkat_sound {schema : PacketSchema} (env : RecEnv schema)
    {z y : NetKAT schema} (h : NetKAT.Derives z y) (p : DyNetKAT schema) :
    Bisimilar env (.nSeq z p) (.nSeq y p) :=
  nSeq_bisimilar_of_historySemantics env p h.historySound

/-- A packet prefix may be rendered as a finite choice of its atomic
complete-test/assignment prefixes, all with the same continuation. -/
theorem packetHeads_bisimilar {schema : PacketSchema} [DiagramLayout schema] (env : RecEnv schema)
    (policy : NetKAT schema) (continuation : DyNetKAT schema) :
    Bisimilar env (.nSeq policy continuation)
      (choiceOf ((symbolicPairsFor policy).map fun pair => .nSeq (packetSummand pair) continuation)) := by
  apply bisimilar_of_step_iff
  intro pending handled action next pending' handled'
  rw [choiceOf_step_iff]
  constructor
  · intro step
    cases step with
    | cpol_seq_ok _ _ i o tail done evaluates =>
      have hit := (mem_symbolicPairsFor policy i o).mpr
        ((historySemantics_singleton_iff_packetSemantics ..).mp evaluates)
      refine ⟨.nSeq (packetSummand (i, o)) continuation,
        List.mem_map.mpr ⟨(i, o), hit, rfl⟩, .cpol_seq_ok _ _ _ _ _ _ ?_⟩
      exact (historySemantics_singleton_iff_packetSemantics ..).mpr
        ((packetSummand_sem i o _).mpr rfl)
  · rintro ⟨_, hb, step⟩
    obtain ⟨pair, hit, rfl⟩ := List.mem_map.mp hb
    cases step with
    | cpol_seq_ok _ _ i o tail done evaluates =>
      have eq := (packetSummand_sem i o pair).mp
        ((historySemantics_singleton_iff_packetSemantics ..).mp evaluates)
      subst pair
      exact .cpol_seq_ok _ _ _ _ _ _ ((historySemantics_singleton_iff_packetSemantics ..).mpr
        ((mem_symbolicPairsFor policy i o).mp hit))

theorem a2_sound (env : RecEnv schema) (p q : DyNetKAT schema) :
    Bisimilar env (.choice p q) (.choice q p) := by
  apply bisimilar_of_step_iff
  intros
  simp only [choice_step_iff, or_comm]

theorem a3_sound (env : RecEnv schema) (p q r : DyNetKAT schema) :
    Bisimilar env (.choice (.choice p q) r) (.choice p (.choice q r)) := by
  apply bisimilar_of_step_iff
  intros
  simp only [choice_step_iff, or_assoc]

theorem a4_sound (env : RecEnv schema) (p : DyNetKAT schema) : Bisimilar env (.choice p p) p := by
  apply bisimilar_of_step_iff
  intros
  simp only [choice_step_iff, or_self]

theorem a5_sound (env : RecEnv schema) (p : DyNetKAT schema) :
    Bisimilar env (.choice p .deadlock) p := by
  apply bisimilar_of_step_iff
  intro pt hl a r pt' hl'
  rw [choice_step_iff, or_iff_left]
  exact deadlock_no_step env pt hl a _

theorem a6_sound (env : RecEnv schema) (p q : DyNetKAT schema) :
    Bisimilar env (.parallel p q) (.parallel q p) := by
  let R (s t : DyNetKAT schema) := ∃ x y, s = .parallel x y ∧ t = .parallel y x
  refine ⟨R, ⟨?_, ?_⟩, p, q, rfl, rfl⟩
  · rintro _ _ ⟨x, y, rfl, rfl⟩
    exact ⟨y, x, rfl, rfl⟩
  · rintro _ _ ⟨x, y, rfl, rfl⟩ pt hl a r pt' hl' hs
    cases hs with
    | cpol_par_l _ _ _ _ _ _ _ _ h => exact ⟨_, .cpol_par_r _ _ _ _ _ _ _ _ h, _, _, rfl, rfl⟩
    | cpol_par_r _ _ _ _ _ _ _ _ h => exact ⟨_, .cpol_par_l _ _ _ _ _ _ _ _ h, _, _, rfl, rfl⟩
    | cpol_sync_recv_send _ _ _ _ _ _ _ _ h k =>
      exact ⟨_, .cpol_sync_send_recv _ _ _ _ _ _ _ _ k h, _, _, rfl, rfl⟩
    | cpol_sync_send_recv _ _ _ _ _ _ _ _ h k =>
      exact ⟨_, .cpol_sync_recv_send _ _ _ _ _ _ _ _ k h, _, _, rfl, rfl⟩

theorem a7_sound (env : RecEnv schema) (p : DyNetKAT schema) :
    Bisimilar env (.parallel p .deadlock) p := by
  let R (s t : DyNetKAT schema) := s = .parallel t .deadlock ∨ t = .parallel s .deadlock
  refine ⟨R, ⟨fun _ _ h => h.symm, ?_⟩, Or.inl rfl⟩
  rintro s t (rfl | rfl) pt hl a r pt' hl' hs
  · cases hs with
    | cpol_par_l _ _ _ _ _ _ _ _ h => exact ⟨_, h, Or.inl rfl⟩
    | cpol_par_r _ _ _ _ _ _ _ _ h => cases h
    | cpol_sync_recv_send _ _ _ _ _ _ _ _ _ h => cases h
    | cpol_sync_send_recv _ _ _ _ _ _ _ _ _ h => cases h
  · exact ⟨_, .cpol_par_l _ _ _ _ _ _ _ _ hs, Or.inr rfl⟩

theorem a8_sound (env : RecEnv schema) (p q : DyNetKAT schema) :
    Bisimilar env (.parallel p q)
      (.choice (.choice (.leftMerge p q) (.leftMerge q p)) (.commMerge p q)) := by
  apply bisimilar_of_matches
  · intro pt hl a r pt' hl' hs
    cases hs with
    | cpol_par_l _ _ _ _ _ _ _ _ h =>
      exact ⟨_, choice_step_iff.mpr (.inl (choice_step_iff.mpr (.inl
        (.cpol_left_merge _ _ _ _ _ _ _ _ h)))), Bisimilar.refl env _⟩
    | cpol_par_r _ _ _ _ _ _ _ _ h =>
      exact ⟨_, choice_step_iff.mpr (.inl (choice_step_iff.mpr (.inr
        (.cpol_left_merge _ _ _ _ _ _ _ _ h)))), a6_sound env _ _⟩
    | cpol_sync_recv_send _ _ _ _ _ _ _ _ h k =>
      exact ⟨_, choice_step_iff.mpr (.inr (.cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ h k)),
        Bisimilar.refl env _⟩
    | cpol_sync_send_recv _ _ _ _ _ _ _ _ h k =>
      exact ⟨_, choice_step_iff.mpr (.inr (.cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ h k)),
        Bisimilar.refl env _⟩
  · intro pt hl a r pt' hl' hs
    rcases choice_step_iff.mp hs with hs | hs
    · rcases choice_step_iff.mp hs with hs | hs
      · cases hs with
        | cpol_left_merge _ _ _ _ _ _ _ _ h =>
          exact ⟨_, .cpol_par_l _ _ _ _ _ _ _ _ h, Bisimilar.refl env _⟩
      · cases hs with
        | cpol_left_merge _ _ _ _ _ _ _ _ h =>
          exact ⟨_, .cpol_par_r _ _ _ _ _ _ _ _ h, a6_sound env _ _⟩
    · cases hs with
      | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ h k =>
        exact ⟨_, .cpol_sync_recv_send _ _ _ _ _ _ _ _ h k, Bisimilar.refl env _⟩
      | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ h k =>
        exact ⟨_, .cpol_sync_send_recv _ _ _ _ _ _ _ _ h k, Bisimilar.refl env _⟩

theorem a9_sound (env : RecEnv schema) (p : DyNetKAT schema) :
    Bisimilar env (.leftMerge .deadlock p) .deadlock := by
  apply bisimilar_of_no_steps
  · intro pt hl a d hs
    cases hs with
    | cpol_left_merge _ _ _ _ _ _ _ _ h => cases h
  · exact deadlock_no_step env

theorem a10_sound (env : RecEnv schema) (l : MoveLabel schema) (p q : DyNetKAT schema) :
    Bisimilar env (.leftMerge (l.prefix p) q) (l.prefix (.parallel p q)) := by
  apply bisimilar_of_step_iff
  intro pt hl a r pt' hl'
  rw [MoveLabel.prefix_step_iff]
  constructor
  · intro hs
    cases hs with
    | cpol_left_merge _ _ _ _ _ _ _ _ h =>
      obtain ⟨rfl, hr⟩ := (MoveLabel.prefix_step_iff ..).mp h
      exact ⟨rfl, hr⟩
  · rintro ⟨rfl, hr⟩
    exact .cpol_left_merge _ _ _ _ _ _ _ _ ((MoveLabel.prefix_step_iff ..).mpr ⟨rfl, hr⟩)

theorem a11_sound (env : RecEnv schema) (p q r : DyNetKAT schema) :
    Bisimilar env (.leftMerge (.choice p q) r) (.choice (.leftMerge p r) (.leftMerge q r)) := by
  apply bisimilar_of_step_iff
  intro pt hl a s pt' hl'
  rw [choice_step_iff]
  constructor
  · intro hs
    cases hs with
    | cpol_left_merge _ _ _ _ _ _ _ _ h =>
      exact (choice_step_iff.mp h).imp
        (Step.cpol_left_merge _ _ _ _ _ _ _ _) (Step.cpol_left_merge _ _ _ _ _ _ _ _)
  · rintro (hs | hs) <;> cases hs
    · exact .cpol_left_merge _ _ _ _ _ _ _ _ (choice_step_iff.mpr (.inl (by assumption)))
    · exact .cpol_left_merge _ _ _ _ _ _ _ _ (choice_step_iff.mpr (.inr (by assumption)))

theorem a12_sound (env : RecEnv schema) (x : Channel) (z : NetKAT schema) (p q : DyNetKAT schema) :
    Bisimilar env (.commMerge (.recv x z p) (.send x z q)) (.rcfgPrefix x z (.parallel p q)) := by
  apply bisimilar_of_step_iff
  intro pt hl a r pt' hl'
  constructor
  · intro hs
    cases hs with
    | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ h k =>
      cases h
      cases k
      exact .cpol_rcfg _ _ _ _ _
    | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ h _ => cases h
  · intro hs
    cases hs
    exact .cpol_comm_merge_recv_send _ _ _ _ _ _ _ _
      (.cpol_recv _ _ _ _ _) (.cpol_send _ _ _ _ _)

theorem a13_sound (env : RecEnv schema) (p q r : DyNetKAT schema) :
    Bisimilar env (.commMerge (.choice p q) r) (.choice (.commMerge p r) (.commMerge q r)) := by
  apply bisimilar_of_step_iff
  intro pt hl a s pt' hl'
  rw [choice_step_iff]
  constructor
  · intro hs
    cases hs with
    | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ h k =>
      exact (choice_step_iff.mp h).imp
        (fun h => .cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ h k)
        (fun h => .cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ h k)
    | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ h k =>
      exact (choice_step_iff.mp h).imp
        (fun h => .cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ h k)
        (fun h => .cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ h k)
  · rintro (hs | hs) <;> cases hs
    · exact .cpol_comm_merge_recv_send _ _ _ _ _ _ _ _
        (choice_step_iff.mpr (.inl (by assumption))) (by assumption)
    · exact .cpol_comm_merge_send_recv _ _ _ _ _ _ _ _
        (choice_step_iff.mpr (.inl (by assumption))) (by assumption)
    · exact .cpol_comm_merge_recv_send _ _ _ _ _ _ _ _
        (choice_step_iff.mpr (.inr (by assumption))) (by assumption)
    · exact .cpol_comm_merge_send_recv _ _ _ _ _ _ _ _
        (choice_step_iff.mpr (.inr (by assumption))) (by assumption)

theorem a14_sound (env : RecEnv schema) (p q : DyNetKAT schema) :
    Bisimilar env (.commMerge p q) (.commMerge q p) := by
  have swap (x y : DyNetKAT schema) : ∀ pt hl a r pt' hl',
      Step env ⟨.commMerge x y, pt, hl⟩ a ⟨r, pt', hl'⟩ →
      ∃ s, Step env ⟨.commMerge y x, pt, hl⟩ a ⟨s, pt', hl'⟩ ∧ Bisimilar env r s := by
    intro pt hl a r pt' hl' hs
    cases hs with
    | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ h k =>
      exact ⟨_, .cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ k h, a6_sound env _ _⟩
    | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ h k =>
      exact ⟨_, .cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ k h, a6_sound env _ _⟩
  exact bisimilar_of_matches env _ _ (swap p q) (swap q p)

/-- Appendix A (96)–(100), and the deadlock case of the printed otherwise rule.
Swapped operands use A14. -/
inductive CommMismatch {schema : PacketSchema} : DyNetKAT schema → DyNetKAT schema → Prop
  | packet : CommMismatch (.nSeq z p) q
  | recvRecv : CommMismatch (.recv x z p) (.recv y w q)
  | sendSend : CommMismatch (.send x z p) (.send y w q)
  | recvSend : (x ≠ y ∨ z ≠ w) → CommMismatch (.recv x z p) (.send y w q)
  | rcfg : CommMismatch (.rcfgPrefix x z p) q
  | deadlock : CommMismatch .deadlock q

theorem a15_sound (env : RecEnv schema) {p q : DyNetKAT schema} (h : CommMismatch p q) :
    Bisimilar env (.commMerge p q) .deadlock := by
  apply bisimilar_of_no_steps
  · intro pt hl a d hs
    cases h with
    | packet | rcfg | deadlock =>
      cases hs <;> rename_i left right <;> cases left
    | recvRecv =>
      cases hs with
      | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ _ right => cases right
      | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ left _ => cases left
    | sendSend =>
      cases hs with
      | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ left _ => cases left
      | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ _ right => cases right
    | recvSend mismatch =>
      cases hs with
      | cpol_comm_merge_recv_send _ _ _ _ _ _ _ _ left right =>
        cases left
        cases right
        exact mismatch.elim (fun h => h rfl) (fun h => h rfl)
      | cpol_comm_merge_send_recv _ _ _ _ _ _ _ _ left _ => cases left
  · exact deadlock_no_step env

/-- Figure 11's narrower `at` sort. Its packet branch is a complete
test followed by a complete assignment. -/
inductive AtomicPrefix {schema : PacketSchema} [DiagramLayout schema] : MoveLabel schema → Prop
  | packet (α π : schema.Packet) :
      AtomicPrefix (.visible (.packet (packetSummand (α, π))))
  | recv (x : Channel) (z : NetKAT schema) : AtomicPrefix (.recv x z)
  | send (x : Channel) (z : NetKAT schema) : AtomicPrefix (.send x z)
  | rcfg (x : Channel) (z : NetKAT schema) : AtomicPrefix (.visible (.rcfg x z))

/-- Only sends and receives are members of a restriction set. -/
def PrefixBlocked (L : Set (CommunicationAction schema)) : MoveLabel schema → Prop
  | .recv x z => .recv x z ∈ L
  | .send x z => .send x z ∈ L
  | .visible _ => False

theorem restrict_prefix_allowed_sound (env : RecEnv schema) (L : Set (CommunicationAction schema))
    (l : MoveLabel schema) (p : DyNetKAT schema) (h : ¬ PrefixBlocked L l) :
    Bisimilar env (.restrict L (l.prefix p)) (l.prefix (.restrict L p)) := by
  cases l with
  | visible l =>
    cases l with
    | packet => exact restrict_nSeq_bisim env L _ p
    | rcfg => exact restrict_rcfgPrefix_bisim env L _ _ p
  | recv => exact restrict_recv_allowed_bisim env L _ _ p h
  | send => exact restrict_send_allowed_bisim env L _ _ p h

theorem restrict_prefix_blocked_sound (env : RecEnv schema) (L : Set (CommunicationAction schema))
    (l : MoveLabel schema) (p : DyNetKAT schema) (h : PrefixBlocked L l) :
    Bisimilar env (.restrict L (l.prefix p)) .deadlock := by
  cases l with
  | visible => exact False.elim h
  | recv => exact restrict_recv_blocked_bisim env L _ _ p h
  | send => exact restrict_send_blocked_bisim env L _ _ p h

theorem project_prefix_sound (env : RecEnv schema) (n : Nat) (l : MoveLabel schema) (p : DyNetKAT schema) :
    Bisimilar env (.project (n + 1) (l.prefix p)) (l.prefix (.project n p)) := by
  cases l with
  | visible l =>
    cases l with
    | packet => exact project_nSeq_bisim env n _ p
    | rcfg => exact project_rcfgPrefix_bisim env n _ _ p
  | recv => exact project_recv_bisim env n _ _ p
  | send => exact project_send_bisim env n _ _ p

theorem prefix_congr (env : RecEnv schema) (l : MoveLabel schema) {p q : DyNetKAT schema}
    (h : Bisimilar env p q) : Bisimilar env (l.prefix p) (l.prefix q) := by
  cases l with
  | visible l =>
    cases l with
    | packet => exact Bisimilar.nSeq_left env h
    | rcfg => exact Bisimilar.rcfgPrefix_left env h
  | recv => exact Bisimilar.recv_left env h
  | send => exact Bisimilar.send_left env h

theorem unfold_sound (env : RecEnv schema) {x : Var} {p : DyNetKAT schema}
    (h : env.lookup x = some p) : Bisimilar env (.var x) p := by
  apply bisimilar_of_step_iff
  intro pt hl a r pt' hl'
  constructor
  · intro hs
    cases hs with
    | cpol_var _ b _ _ _ _ _ _ he hs =>
      obtain rfl := Option.some.inj (he.symm.trans h)
      exact hs
  · exact .cpol_var _ _ _ _ _ _ _ _ h

end Equations

open Equations

/-- The typed non-AIP equational system. Process contexts keep all payloads,
restriction sets, and projection depths fixed. Named definitions refer to
the same environment on both sides. -/
inductive DerivesNoAIP {schema : PacketSchema} (env : RecEnv schema) : DyNetKAT schema → DyNetKAT schema → Prop
  | refl (p) : DerivesNoAIP env p p
  | symm : DerivesNoAIP env p q → DerivesNoAIP env q p
  | trans : DerivesNoAIP env p q → DerivesNoAIP env q r → DerivesNoAIP env p r
  | prefixCongr (l : MoveLabel schema) : DerivesNoAIP env p q →
      DerivesNoAIP env (l.prefix p) (l.prefix q)
  | choiceCongr : DerivesNoAIP env p p' → DerivesNoAIP env q q' →
      DerivesNoAIP env (.choice p q) (.choice p' q')
  | parallelCongr : DerivesNoAIP env p p' → DerivesNoAIP env q q' →
      DerivesNoAIP env (.parallel p q) (.parallel p' q')
  | leftMergeCongr : DerivesNoAIP env p p' → DerivesNoAIP env q q' →
      DerivesNoAIP env (.leftMerge p q) (.leftMerge p' q')
  | commMergeCongr : DerivesNoAIP env p p' → DerivesNoAIP env q q' →
      DerivesNoAIP env (.commMerge p q) (.commMerge p' q')
  | restrictCongr (L : Set (CommunicationAction schema)) : DerivesNoAIP env p q →
      DerivesNoAIP env (.restrict L p) (.restrict L q)
  | projectCongr (n : Nat) : DerivesNoAIP env p q →
      DerivesNoAIP env (.project n p) (.project n q)
  | unfold : env.lookup x = some p → DerivesNoAIP env (.var x) p
  | netkat (p : DyNetKAT schema) : NetKAT.Derives z y → DerivesNoAIP env (.nSeq z p) (.nSeq y p)
  | a0 (p) : DerivesNoAIP env (.nSeq .drop p) .deadlock
  | a1 (z y p) : DerivesNoAIP env (.nSeq (.union z y) p) (.choice (.nSeq z p) (.nSeq y p))
  | a2 (p q) : DerivesNoAIP env (.choice p q) (.choice q p)
  | a3 (p q r) : DerivesNoAIP env (.choice (.choice p q) r) (.choice p (.choice q r))
  | a4 (p) : DerivesNoAIP env (.choice p p) p
  | a5 (p) : DerivesNoAIP env (.choice p .deadlock) p
  | a6 (p q) : DerivesNoAIP env (.parallel p q) (.parallel q p)
  | a7 (p) : DerivesNoAIP env (.parallel p .deadlock) p
  | a8 (p q) : DerivesNoAIP env (.parallel p q)
      (.choice (.choice (.leftMerge p q) (.leftMerge q p)) (.commMerge p q))
  | a9 (p) : DerivesNoAIP env (.leftMerge .deadlock p) .deadlock
  | a10 (l : MoveLabel schema) (p q) : DerivesNoAIP env (.leftMerge (l.prefix p) q)
      (l.prefix (.parallel p q))
  | a11 (p q r) : DerivesNoAIP env (.leftMerge (.choice p q) r)
      (.choice (.leftMerge p r) (.leftMerge q r))
  | a12 (x z p q) : DerivesNoAIP env (.commMerge (.recv x z p) (.send x z q))
      (.rcfgPrefix x z (.parallel p q))
  | a13 (p q r) : DerivesNoAIP env (.commMerge (.choice p q) r)
      (.choice (.commMerge p r) (.commMerge q r))
  | a14 (p q) : DerivesNoAIP env (.commMerge p q) (.commMerge q p)
  | a15 : CommMismatch p q → DerivesNoAIP env (.commMerge p q) .deadlock
  | restrictDeadlock (L) : DerivesNoAIP env (.restrict L .deadlock) .deadlock
  | restrictAllowed {layout : DiagramLayout schema} (L l p) : @AtomicPrefix schema layout l → (¬ PrefixBlocked L l) →
      DerivesNoAIP env (.restrict L (l.prefix p)) (l.prefix (.restrict L p))
  | restrictBlocked {layout : DiagramLayout schema} (L l p) : @AtomicPrefix schema layout l → PrefixBlocked L l →
      DerivesNoAIP env (.restrict L (l.prefix p)) .deadlock
  | restrictChoice (L p q) : DerivesNoAIP env (.restrict L (.choice p q))
      (.choice (.restrict L p) (.restrict L q))
  | projectZero (p) : DerivesNoAIP env (.project 0 p) .deadlock
  | projectDeadlock (n) : DerivesNoAIP env (.project n .deadlock) .deadlock
  | projectPrefix {layout : DiagramLayout schema} (n l p) : @AtomicPrefix schema layout l →
      DerivesNoAIP env (.project (n + 1) (l.prefix p)) (l.prefix (.project n p))
  | projectChoice (n p q) : DerivesNoAIP env (.project n (.choice p q))
      (.choice (.project n p) (.project n q))

theorem DerivesNoAIP.a12_reverse (env : RecEnv schema) (x : Channel) (z : NetKAT schema)
    (p q : DyNetKAT schema) : DerivesNoAIP env (.commMerge (.send x z p) (.recv x z q))
      (.rcfgPrefix x z (.parallel p q)) :=
  .trans (.a14 _ _) (.trans (.a12 _ _ _ _) (.prefixCongr (.visible (.rcfg x z)) (.a6 _ _)))

/-- Soundness of the typed non-AIP system, with literal action labels and
both initial and final packet lists preserved by strong bisimilarity. -/
theorem DerivesNoAIP.sound {env : RecEnv schema} {p q : DyNetKAT schema}
    (h : DerivesNoAIP env p q) : Bisimilar env p q := by
  induction h with
  | refl => exact Bisimilar.refl env _
  | symm _ ih => exact Bisimilar.symm env ih
  | trans _ _ ih₁ ih₂ => exact Bisimilar.trans env ih₁ ih₂
  | prefixCongr l _ ih => exact prefix_congr env l ih
  | choiceCongr _ _ ih₁ ih₂ =>
    exact Bisimilar.trans env (Bisimilar.choice_left env ih₁) (Bisimilar.choice_right env ih₂)
  | parallelCongr _ _ ih₁ ih₂ =>
    exact Bisimilar.trans env (Bisimilar.parallel_right env ih₁) (Bisimilar.parallel_left env ih₂)
  | leftMergeCongr _ _ ih₁ ih₂ =>
    exact Bisimilar.trans env (Bisimilar.leftMerge_left env ih₁) (Bisimilar.leftMerge_right env ih₂)
  | commMergeCongr _ _ ih₁ ih₂ =>
    exact Bisimilar.trans env (Bisimilar.commMerge_right env ih₁) (Bisimilar.commMerge_left env ih₂)
  | restrictCongr _ _ ih => exact Bisimilar.restrict env ih
  | projectCongr _ _ ih => exact Bisimilar.project env ih
  | unfold h => exact unfold_sound env h
  | netkat p h => exact netkat_sound env h p
  | a0 => exact a0_sound env _
  | a1 => exact a1_sound env _ _ _
  | a2 => exact a2_sound env _ _
  | a3 => exact a3_sound env _ _ _
  | a4 => exact a4_sound env _
  | a5 => exact a5_sound env _
  | a6 => exact a6_sound env _ _
  | a7 => exact a7_sound env _
  | a8 => exact a8_sound env _ _
  | a9 => exact a9_sound env _
  | a10 => exact a10_sound env _ _ _
  | a11 => exact a11_sound env _ _ _
  | a12 => exact a12_sound env _ _ _ _
  | a13 => exact a13_sound env _ _ _
  | a14 => exact a14_sound env _ _
  | a15 h => exact a15_sound env h
  | restrictDeadlock => exact restrict_deadlock_bisim env _
  | restrictAllowed _ _ _ _ h => exact restrict_prefix_allowed_sound env _ _ _ h
  | restrictBlocked _ _ _ _ h => exact restrict_prefix_blocked_sound env _ _ _ h
  | restrictChoice => exact restrict_choice_bisim env _ _ _
  | projectZero => exact project_zero_bisim env _
  | projectDeadlock => exact project_deadlock_bisim env _
  | projectPrefix => exact project_prefix_sound env _ _ _
  | projectChoice => exact project_choice_bisim env _ _ _

end DyNetKAT.DyNetKAT
