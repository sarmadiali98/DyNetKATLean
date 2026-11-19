import DyNetKAT.DyNetKAT.GraphTail
import DyNetKAT.DyNetKAT.GraphRestriction

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

/-- Sequential normal forms with an actual packet move available at every
packet prefix. The condition is relational and uses no packet enumeration. -/
inductive EnabledSequential (G : ProcessGraph) : GProc → Prop
  | deadlock : EnabledSequential G .deadlock
  | packet : (∃ i o, Semantics N i o) → EnabledSequential G p →
      EnabledSequential G (.nSeq N p)
  | rcfg : EnabledSequential G p → EnabledSequential G (.rcfgPrefix x N p)
  | choice : EnabledSequential G p → EnabledSequential G q → EnabledSequential G (.choice p q)
  | ref : i ∈ G.nodes → EnabledSequential G (.ref i)

structure TraceReady (G : ProcessGraph) : Prop where
  root : EnabledSequential G G.root
  label : ∀ i ∈ G.nodes, EnabledSequential G (G.label i)

theorem EnabledSequential.shape {G : ProcessGraph} {p : GProc} (h : EnabledSequential G p) :
    TailShapeOk G p := by
  induction h with
  | deadlock => exact .deadlock
  | packet _ _ ih => exact .nSeq ih
  | rcfg _ ih => exact .rcfgPrefix ih
  | choice _ _ ih₁ ih₂ => exact .choice ih₁ ih₂
  | ref mem => exact .ref mem

theorem EnabledSequential.mono {G Q : ProcessGraph} {p : GProc} (nodes : G.nodes ⊆ Q.nodes)
    (h : EnabledSequential G p) : EnabledSequential Q p := by
  induction h with
  | deadlock => exact .deadlock
  | packet ev _ ih => exact .packet ev ih
  | rcfg _ ih => exact .rcfg ih
  | choice _ _ ih₁ ih₂ => exact .choice ih₁ ih₂
  | ref mem => exact .ref (nodes mem)

theorem GStep.enabledSequential {G : ProcessGraph} {c d : GConfig} {a : Action}
    (ready : TraceReady G) (step : GStep G c a d) :
    EnabledSequential G c.proc → EnabledSequential G d.proc := by
  induction step with
  | seq_ok => intro h; cases h; assumption
  | rcfg => intro h; cases h; assumption
  | choice_l _ _ _ _ _ _ _ _ _ ih => intro h; cases h; exact ih (by assumption)
  | choice_r _ _ _ _ _ _ _ _ _ ih => intro h; cases h; exact ih (by assumption)
  | var i _ _ _ _ _ _ _ ih => intro h; cases h; exact ih (ready.label i (by assumption))
  | recv | send | par_l | par_r | left_merge | comm_merge_recv_send | comm_merge_send_recv |
    sync_recv_send | sync_send_recv | project | restrict => intro h; cases h

theorem GraphPath.enabledSequential {G : ProcessGraph} {p q : GProc} {w : List Action}
    (ready : TraceReady G) (run : GraphPath G p w q) (shape : EnabledSequential G p) :
    EnabledSequential G q := by
  induction w generalizing p with
  | nil => obtain rfl := GraphPath.nil_iff.mp run; exact shape
  | cons a w ih =>
      obtain ⟨mid, step, rest⟩ := GraphPath.cons_iff.mp run
      exact ih rest (GStep.enabledSequential ready step shape)

theorem GraphPath.map_first {G : ProcessGraph} {p p' q : GProc} {w : List Action}
    (run : GraphPath G p w q) (nonempty : w ≠ [])
    (transfer : ∀ a mid, GraphActionStep G p a mid → GraphActionStep G p' a mid) :
    GraphPath G p' w q := by
  cases w with
  | nil => exact (nonempty rfl).elim
  | cons a rest =>
      obtain ⟨mid, first, succ⟩ := GraphPath.cons_iff.mp run
      exact GraphPath.cons_iff.mpr ⟨mid, transfer a mid first, succ⟩

theorem GraphActionStep.packet {G : ProcessGraph} {N : NetKAT} {p : GProc} {i o : CtxPkt}
    (ev : Semantics N i o) : GraphActionStep G (.nSeq N p) (.packet i o) p :=
  .seq_ok _ _ _ _ [] [] ((historySemantics_singleton_iff_packetSemantics ..).mpr ev)

theorem GraphPath.single {G : ProcessGraph} {p q : GProc} {a : Action}
    (step : GraphActionStep G p a q) : GraphPath G p [a] q :=
  GraphPath.cons_iff.mpr ⟨q, step, GraphPath.nil_iff.mpr rfl⟩

/-- Visible labels preceding the final packet in a head query. -/
def PacketAction : Action → Prop
  | .packet .. => True
  | _ => False

def SelectedReconfig (R : ReconfigSet) : Action → Prop
  | .rcfg x N => (x, N) ∈ R
  | _ => False

/-- A nonempty segment through the selected region, ending at a selected
reconfiguration. Intermediate packet steps and selected reconfigurations
are allowed by the structural equations. -/
inductive TailWord (R : ReconfigSet) : List Action → Prop
  | last : (x, N) ∈ R → TailWord R [.rcfg x N]
  | packet : TailWord R w → TailWord R (.packet i o :: w)
  | rcfg : (x, N) ∈ R → TailWord R w → TailWord R (.rcfg x N :: w)

theorem TailWord.nonempty {R : ReconfigSet} {w : List Action} (h : TailWord R w) : w ≠ [] := by
  cases h <;> simp

theorem TailSelect.feasible {G : ProcessGraph} {R : ReconfigSet} {p q : GProc}
    (ready : TraceReady G) (h : TailSelect G R p q) :
    EnabledSequential G p → ∃ w, TailWord R w ∧ GraphPath G p w q := by
  induction h with
  | packet _ ih =>
      intro shape
      cases shape with
      | packet enabled shape =>
          obtain ⟨i, o, ev⟩ := enabled
          obtain ⟨w, word, run⟩ := ih shape
          exact ⟨_ , .packet word, GraphPath.cons_iff.mpr ⟨_, .packet ev, run⟩⟩
  | left _ ih =>
      intro shape
      cases shape with
      | choice shape _ =>
          obtain ⟨w, word, run⟩ := ih shape
          exact ⟨w, word, run.map_first word.nonempty (fun _ _ s => .choice_l _ _ _ _ _ _ _ _ s)⟩
  | right _ ih =>
      intro shape
      cases shape with
      | choice _ shape =>
          obtain ⟨w, word, run⟩ := ih shape
          exact ⟨w, word, run.map_first word.nonempty (fun _ _ s => .choice_r _ _ _ _ _ _ _ _ s)⟩
  | ref _ ih =>
      intro shape
      cases shape with
      | ref mem =>
          obtain ⟨w, word, run⟩ := ih (ready.label _ mem)
          exact ⟨w, word, run.map_first word.nonempty (fun _ _ s => .var _ _ _ _ _ _ _ s)⟩
  | stop mem =>
      exact fun _ => ⟨_, .last mem, GraphPath.single (.rcfg _ _ _ [] [])⟩
  | next mem _ ih =>
      intro shape
      cases shape with
      | rcfg shape =>
          obtain ⟨w, word, run⟩ := ih shape
          exact ⟨_, .rcfg mem word, GraphPath.cons_iff.mpr ⟨_, .rcfg _ _ _ [] [], run⟩⟩

private theorem tail_of_step {G : ProcessGraph} {R : ReconfigSet} {c d : GConfig} {a : Action}
    {q : GProc} (ready : TraceReady G) (step : GStep G c a d) :
    EnabledSequential G c.proc →
      ((SelectedReconfig R a ∧ d.proc = q) ∨
        ((PacketAction a ∨ SelectedReconfig R a) ∧ TailSelect G R d.proc q)) →
      TailSelect G R c.proc q := by
  induction step with
  | seq_ok =>
      rintro _ (⟨no, _⟩ | ⟨_, select⟩)
      · exact no.elim
      · exact .packet select
  | rcfg =>
      rintro _ (⟨mem, rfl⟩ | ⟨(no | mem), select⟩)
      · exact .stop mem
      · exact no.elim
      · exact .next mem select
  | choice_l _ _ _ _ _ _ _ _ _ ih =>
      intro shape h; cases shape; exact .left (ih (by assumption) h)
  | choice_r _ _ _ _ _ _ _ _ _ ih =>
      intro shape h; cases shape; exact .right (ih (by assumption) h)
  | var i _ _ _ _ _ _ _ ih =>
      intro shape h; cases shape; exact .ref (ih (ready.label i (by assumption)) h)
  | recv | send | par_l | par_r | left_merge | comm_merge_recv_send | comm_merge_send_recv |
    sync_recv_send | sync_send_recv | project | restrict => intro h; cases h

theorem TailWord.select {G : ProcessGraph} {R : ReconfigSet} {p q : GProc} {w : List Action}
    (ready : TraceReady G) (word : TailWord R w) (run : GraphPath G p w q)
    (shape : EnabledSequential G p) : TailSelect G R p q := by
  induction word generalizing p with
  | last mem =>
      obtain ⟨mid, first, rest⟩ := GraphPath.cons_iff.mp run
      exact tail_of_step ready first shape (.inl ⟨mem, GraphPath.nil_iff.mp rest⟩)
  | packet _ ih =>
      obtain ⟨mid, first, rest⟩ := GraphPath.cons_iff.mp run
      exact tail_of_step ready first shape (.inr ⟨.inl trivial,
        ih rest (GStep.enabledSequential ready first shape)⟩)
  | rcfg mem _ ih =>
      obtain ⟨mid, first, rest⟩ := GraphPath.cons_iff.mp run
      exact tail_of_step ready first shape (.inr ⟨.inr mem,
        ih rest (GStep.enabledSequential ready first shape)⟩)

private theorem head_feasible {G : ProcessGraph} {p : GProc} {i o : CtxPkt}
    (ready : TraceReady G) (h : GraphHeadSpec G p i o) :
    EnabledSequential G p → ∃ w q, w.Forall PacketAction ∧
      GraphPath G p (w ++ [.packet i o]) q := by
  induction h with
  | nSeq_of_sem _ p _ _ ev =>
      exact fun _ => ⟨[], p, trivial, GraphPath.single (.packet ev)⟩
  | nSeq_of_tail _ _ _ _ _ ih =>
      intro shape
      cases shape with
      | packet enabled shape =>
          obtain ⟨σ, τ, ev⟩ := enabled
          obtain ⟨w, q, word, run⟩ := ih shape
          exact ⟨.packet σ τ :: w, q, (List.forall_cons ..).mpr ⟨trivial, word⟩,
            GraphPath.cons_iff.mpr ⟨_, .packet ev, run⟩⟩
  | choice_left _ _ _ _ _ ih =>
      intro shape
      cases shape with
      | choice shape _ =>
          obtain ⟨w, q, word, run⟩ := ih shape
          exact ⟨w, q, word, run.map_first (by simp) (fun _ _ s => .choice_l _ _ _ _ _ _ _ _ s)⟩
  | choice_right _ _ _ _ _ ih =>
      intro shape
      cases shape with
      | choice _ shape =>
          obtain ⟨w, q, word, run⟩ := ih shape
          exact ⟨w, q, word, run.map_first (by simp) (fun _ _ s => .choice_r _ _ _ _ _ _ _ _ s)⟩
  | ref_of k _ _ _ ih =>
      intro shape
      cases shape with
      | ref mem =>
          obtain ⟨w, q, word, run⟩ := ih (ready.label k mem)
          exact ⟨w, q, word, run.map_first (by simp) (fun _ _ s => .var _ _ _ _ _ _ _ s)⟩

private theorem head_of_step {G : ProcessGraph} {c d : GConfig} {a : Action}
    {i o : CtxPkt} (ready : TraceReady G) (step : GStep G c a d) :
    EnabledSequential G c.proc →
      (a = .packet i o ∨ (PacketAction a ∧ GraphHeadSpec G d.proc i o)) →
      GraphHeadSpec G c.proc i o := by
  induction step with
  | seq_ok _ _ _ _ _ _ ev =>
      rintro _ (eq | ⟨_, head⟩)
      · cases eq
        exact .nSeq_of_sem _ _ _ _ ((historySemantics_singleton_iff_packetSemantics ..).mp ev)
      · exact .nSeq_of_tail _ _ _ _ head
  | rcfg => rintro _ (eq | ⟨no, _⟩); cases eq; exact no.elim
  | choice_l _ _ _ _ _ _ _ _ _ ih =>
      intro shape h; cases shape; exact .choice_left _ _ _ _ (ih (by assumption) h)
  | choice_r _ _ _ _ _ _ _ _ _ ih =>
      intro shape h; cases shape; exact .choice_right _ _ _ _ (ih (by assumption) h)
  | var k _ _ _ _ _ _ _ ih =>
      intro shape h; cases shape; exact .ref_of _ _ _ (ih (ready.label k (by assumption)) h)
  | recv | send | par_l | par_r | left_merge | comm_merge_recv_send | comm_merge_send_recv |
    sync_recv_send | sync_send_recv | project | restrict => intro h; cases h

theorem GraphHeadSpec.iff_feasible {G : ProcessGraph} {p : GProc} {i o : CtxPkt}
    (ready : TraceReady G) (shape : EnabledSequential G p) :
    GraphHeadSpec G p i o ↔ ∃ w q, w.Forall PacketAction ∧
      GraphPath G p (w ++ [.packet i o]) q := by
  refine ⟨fun h => head_feasible ready h shape, ?_⟩
  rintro ⟨w, q, word, run⟩
  induction w generalizing p with
  | nil =>
      obtain ⟨_, step, _⟩ := GraphPath.cons_iff.mp run
      exact head_of_step ready step shape (.inl rfl)
  | cons a w ih =>
      obtain ⟨mid, first, rest⟩ := GraphPath.cons_iff.mp run
      exact head_of_step ready first shape (.inr ⟨((List.forall_cons ..).mp word).1,
        ih (GStep.enabledSequential ready first shape) ((List.forall_cons ..).mp word).2 rest⟩)


private theorem tailCollect_enabled {G Q : ProcessGraph} {R : ReconfigSet} {L : List NodeId}
    (original : G.nodes ⊆ Q.nodes)
    (renamed : ∀ i ∈ L, fresh G L i ∈ Q.nodes) {p : GProc} (shape : EnabledSequential G p) :
    ∀ {q}, tailCollectR G R (fresh G L) p = some q →
      (∀ i ∈ tailRefsR R p, i ∈ L) → EnabledSequential Q q := by
  induction shape with
  | deadlock => intro q eq _; cases eq; exact .deadlock
  | packet ev body ih => exact fun eq live => ih eq live
  | choice hL hR ihL ihR =>
      intro q eq live
      obtain ⟨l, r, h₁, h₂, rfl⟩ := tailCollectR_choice_some_iff.mp eq
      exact .choice (ihL h₁ (fun i hi => live i (List.mem_append_left _ hi)))
        (ihR h₂ (fun i hi => live i (List.mem_append_right _ hi)))
  | @rcfg p x N shape ih =>
      intro q eq live
      by_cases mem : (x, N) ∈ R
      · obtain ⟨r, tailEq, rfl⟩ := (tailCollectR_rcfgPrefix_mem_some_iff mem).mp eq
        exact .choice (shape.mono original) (ih tailEq (by simpa [tailRefsR, mem] using live))
      · rw [tailCollectR_rcfgPrefix_not_mem _ mem] at eq
        cases eq
        exact .deadlock
  | @ref i mem =>
      intro q eq live
      cases eq
      exact .ref (renamed i (live i (by simp [tailRefsR])))

theorem graphTail_traceReady {G Q : ProcessGraph} {R : ReconfigSet}
    (ready : TraceReady G) (h : graphTail G R = some Q) : TraceReady Q := by
  obtain ⟨L, root, entries, hRun, hRoot, hEntries, rfl⟩ := graphTail_some_inv h
  let out := tailGraphOf G R L root entries hRun hRoot hEntries
  have original : G.nodes ⊆ out.nodes := fun _ hi => Finset.mem_union_left _ hi
  have renamed (i : NodeId) (hi : i ∈ L) : fresh G L i ∈ out.nodes :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, List.mem_toFinset.mpr hi, rfl⟩)
  refine ⟨tailCollect_enabled original renamed ready.root hRoot (tailRun_root_refs_mem hRun).1, ?_⟩
  intro i hi
  rcases Finset.mem_union.mp hi with old | new
  · rw [tailGraphOf_label_original old]
    exact (ready.label i old).mono original
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp new
    have mem := List.mem_toFinset.mp hj
    have node := (tailRun_root_success G R L hRun).2.2 j mem
    obtain ⟨q, eq⟩ := Option.ne_none_iff_exists'.mp
      ((collectTailLabels_some_iff _ L).mp ⟨entries, hEntries⟩ j mem)
    rw [tailGraphOf_label_fresh mem eq]
    exact tailCollect_enabled original renamed (ready.label j node) eq
      ((tailRun_root_refs_mem hRun).2 j mem)

theorem graphTail_feasible_iff {G Q : ProcessGraph} {R : ReconfigSet} {w : List Action}
    {dst : GProc} (ready : TraceReady G) (h : graphTail G R = some Q) (nonempty : w ≠ []) :
    GraphPath Q Q.root w dst ↔ ∃ pre, TailWord R pre ∧ GraphPath G G.root (pre ++ w) dst := by
  cases w with
  | nil => exact (nonempty rfl).elim
  | cons a rest =>
      rw [graphTail_path_iff h]
      constructor
      · rintro ⟨p, sel, run⟩
        obtain ⟨pre, word, first⟩ := sel.feasible ready ready.root
        exact ⟨pre, word, GraphPath.append_iff.mpr ⟨p, first, run⟩⟩
      · rintro ⟨pre, word, run⟩
        obtain ⟨p, first, rest⟩ := GraphPath.append_iff.mp run
        exact ⟨p, word.select ready first ready.root, rest⟩

/-- Successive calls use the actual structural tail graph, including its
fresh labels and its preserved original continuations. -/
def graphTails (G : ProcessGraph) : List ReconfigSet → Option ProcessGraph
  | [] => some G
  | R :: rest => (graphTail G R).bind (fun Q => graphTails Q rest)

def TailSegments : List ReconfigSet → List Action → Prop
  | [], w => w = []
  | R :: rest, w => ∃ u v, w = u ++ v ∧ TailWord R u ∧ TailSegments rest v

theorem graphTails_traceReady {G Q : ProcessGraph} {stages : List ReconfigSet}
    (ready : TraceReady G) (tails : graphTails G stages = some Q) : TraceReady Q := by
  induction stages generalizing G with
  | nil => cases tails; exact ready
  | cons R rest ih =>
      obtain ⟨mid, first, last⟩ := Option.bind_eq_some_iff.mp tails
      exact ih (graphTail_traceReady ready first) last

theorem graphTails_feasible_iff {G Q : ProcessGraph} {stages : List ReconfigSet}
    {w : List Action} {dst : GProc} (ready : TraceReady G)
    (tails : graphTails G stages = some Q) (nonempty : w ≠ []) :
    GraphPath Q Q.root w dst ↔ ∃ pre, TailSegments stages pre ∧
      GraphPath G G.root (pre ++ w) dst := by
  induction stages generalizing G with
  | nil => cases tails; simp [TailSegments]
  | cons R rest ih =>
      obtain ⟨mid, first, last⟩ := Option.bind_eq_some_iff.mp tails
      rw [ih (graphTail_traceReady ready first) last]
      constructor
      · rintro ⟨v, segments, run⟩
        have ne : v ++ w ≠ [] := fun eq => nonempty (List.append_eq_nil_iff.mp eq).2
        obtain ⟨u, word, path⟩ := (graphTail_feasible_iff ready first ne).mp run
        exact ⟨u ++ v, ⟨u, v, rfl, word, segments⟩, by simpa [List.append_assoc] using path⟩
      · rintro ⟨_, ⟨u, v, rfl, word, segments⟩, path⟩
        have ne : v ++ w ≠ [] := fun eq => nonempty (List.append_eq_nil_iff.mp eq).2
        exact ⟨v, segments, (graphTail_feasible_iff ready first ne).mpr
          ⟨u, word, by simpa [List.append_assoc] using path⟩⟩

/-- The packet observation belongs to the last step, with its actual input
and output. Earlier packets consume their own inputs. -/
def QueryWord (stages : List ReconfigSet) (i o : CtxPkt) (word : List Action) : Prop :=
  ∃ pre head, TailSegments stages pre ∧ head.Forall PacketAction ∧
    word = pre ++ (head ++ [.packet i o])

theorem graphTails_head_iff {G Q : ProcessGraph} {stages : List ReconfigSet}
    {H : NetKAT} {i o : CtxPkt} (ready : TraceReady G)
    (tails : graphTails G stages = some Q) (head : graphHead Q = some H) :
    Semantics H i o ↔ ∃ w dst, QueryWord stages i o w ∧ GraphPath G G.root w dst := by
  have hReady := graphTails_traceReady ready tails
  constructor
  · intro sem
    obtain ⟨w, dst, packets, run⟩ := (GraphHeadSpec.iff_feasible hReady hReady.root).mp
      (graphHead_sound Q H head i o sem)
    obtain ⟨pre, seg, full⟩ := (graphTails_feasible_iff ready tails
      (w := w ++ [.packet i o]) (by simp)).mp run
    exact ⟨_, dst, ⟨pre, w, seg, packets, rfl⟩, full⟩
  · rintro ⟨_, dst, ⟨pre, w, seg, packets, rfl⟩, run⟩
    apply graphHead_complete Q H head i o
    apply (GraphHeadSpec.iff_feasible hReady hReady.root).mpr
    exact ⟨w, dst, packets, (graphTails_feasible_iff ready tails (by simp)).mpr ⟨pre, seg, run⟩⟩

theorem graphTails_head_exists {G : ProcessGraph} (ready : TraceReady G) (stages : List ReconfigSet) :
    ∃ Q H, graphTails G stages = some Q ∧ graphHead Q = some H := by
  induction stages generalizing G with
  | nil =>
      obtain ⟨H, head⟩ := graphHead_supported_some G
        (graphSupported_of_shapes ready.root.shape (fun i hi => (ready.label i hi).shape)).1
      exact ⟨G, H, rfl, head⟩
  | cons R stages ih =>
      obtain ⟨Q, tail⟩ := graphTail_supported_some (R := R)
        (graphSupported_of_shapes ready.root.shape (fun i hi => (ready.label i hi).shape )).2
      obtain ⟨T, H, tails, head⟩ := ih (graphTail_traceReady ready tail)
      exact ⟨T, H, Option.bind_eq_some_iff.mpr ⟨Q, tail, tails⟩, head⟩

theorem blockCommunication_enabled {Q : ProcessGraph} {p q : GProc}
    (h : blockCommunication p = some q) (hc : gprocRefs q ⊆ Q.nodes) :
    EnabledSequential Q q := by
  induction p generalizing q with
  | nSeq N _ ih =>
      rw [blockCommunication] at h
      split at h
      · cases h; exact .deadlock
      · rename_i nonzero
        obtain ⟨p', hp, rfl⟩ := Option.map_eq_some'.mp h
        have enabled : ∃ i o, Semantics N i o := by
          by_contra disabled
          apply nonzero
          exact (netkatIsZero_correct N).mpr (fun i o ev => disabled ⟨i, o, ev⟩)
        exact .packet enabled (ih hp hc)
  | rcfgPrefix _ _ _ ih =>
      obtain ⟨p', hp, rfl⟩ := Option.map_eq_some'.mp h
      exact .rcfg (ih hp hc)
  | choice _ _ ih₁ ih₂ =>
      obtain ⟨p', hp, rest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨q', hq, rfl⟩ := Option.map_eq_some'.mp rest
      exact .choice (ih₁ hp (Finset.union_subset_iff.mp hc).1)
        (ih₂ hq (Finset.union_subset_iff.mp hc).2)
  | ref i => cases h; exact .ref (hc (Finset.mem_singleton_self i))
  | deadlock | recv | send => cases h; exact .deadlock
  | parallel | leftMerge | commMerge | restrict | project => cases h

theorem preprocessGraph_traceReady {G Q : ProcessGraph} (h : preprocessGraph G = some Q) :
    TraceReady Q := by
  obtain ⟨nodes, root, labels⟩ := preprocessGraph_eq_some h
  exact ⟨blockCommunication_enabled root Q.root_closed, fun i hi =>
    blockCommunication_enabled (labels i (nodes ▸ hi)) (Q.closed i hi)⟩

end DyNetKAT.DyNetKAT
