import DyNetKATLean.Core.ProcessGraph
import DyNetKATLean.Core.NetKATBridge
import NetKATLean.Core.Decision

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : PacketSchema}

open DyNetKAT.NetKAT

/-- Push a restriction of all communication actions through the sequential
    fragment. Synchronizations already represented by reconfiguration prefixes
    survive. Packet prefixes with empty relations are replaced by deadlock.
    Parallel and merge terms require normalization before this pass. -/
def blockCommunication : GProc schema → Option (GProc schema)
  | .deadlock => some .deadlock
  | .nSeq N p => if netkatIsZero N then some .deadlock else (blockCommunication p).map (.nSeq N)
  | .rcfgPrefix x N p => (blockCommunication p).map (.rcfgPrefix x N)
  | .choice p q => (blockCommunication p).bind fun p' =>
      (blockCommunication q).map (.choice p')
  | .recv _ _ _ | .send _ _ _ => some .deadlock
  | .ref i => some (.ref i)
  | .parallel _ _ | .leftMerge _ _ | .commMerge _ _ | .restrict _ _ | .project _ _ => none

theorem blockCommunication_refs {p q : GProc schema} (h : blockCommunication p = some q) :
    gprocRefs q ⊆ gprocRefs p := by
  induction p generalizing q with
  | nSeq N _ ih =>
      rw [blockCommunication] at h
      split at h
      · cases h; simp [gprocRefs]
      · obtain ⟨p', hp, rfl⟩ := Option.map_eq_some'.mp h
        exact ih (q := p') hp
  | rcfgPrefix _ _ _ ih =>
      obtain ⟨p', hp, rfl⟩ := Option.map_eq_some'.mp h
      exact ih (q := p') hp
  | choice _ _ ih₁ ih₂ =>
      obtain ⟨_, hp, he⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, hq, rfl⟩ := Option.map_eq_some'.mp he
      exact Finset.union_subset_union (ih₁ hp) (ih₂ hq)
  | deadlock | recv | send | ref =>
      cases h
      simp [gprocRefs]
  | parallel | leftMerge | commMerge | restrict | project => cases h

private theorem blockCommunication_get (p : GProc schema) (h : (blockCommunication p).isSome) :
    blockCommunication p = some ((blockCommunication p).get h) :=
  (Option.some_get h).symm

private def restrictedGraph (G : ProcessGraph schema) (root : GProc schema)
    (hRoot : blockCommunication G.root = some root)
    (hLabels : ∀ i ∈ G.nodes, (blockCommunication (G.label i)).isSome) : (ProcessGraph schema) where
  nodes := G.nodes
  root := root
  label := fun i => if hi : i ∈ G.nodes then (blockCommunication (G.label i)).get (hLabels i hi)
    else .deadlock
  root_closed := (blockCommunication_refs hRoot).trans G.root_closed
  closed := by
    intro i hi
    rw [dif_pos hi]
    exact (blockCommunication_refs (blockCommunication_get _ (hLabels i hi))).trans
      (G.closed i hi)

/-- Eliminate the outer communication restriction on a closed sequential
    graph. All supplied node labels are checked before a graph is returned. -/
def preprocessGraph (G : ProcessGraph schema) : Option (ProcessGraph schema) :=
  match hRoot : blockCommunication G.root with
  | none => none
  | some root =>
      if hLabels : ∀ i ∈ G.nodes, (blockCommunication (G.label i)).isSome then
        some (restrictedGraph G root hRoot hLabels)
      else none

theorem preprocessGraph_eq_some {G Q : ProcessGraph schema} (h : preprocessGraph G = some Q) :
    Q.nodes = G.nodes ∧ blockCommunication G.root = some Q.root ∧
      ∀ i ∈ G.nodes, blockCommunication (G.label i) = some (Q.label i) := by
  unfold preprocessGraph at h
  split at h
  · contradiction
  · rename_i root hRoot
    split at h
    · rename_i hLabels
      obtain rfl := Option.some.inj h
      refine ⟨rfl, hRoot, fun i hi => ?_⟩
      simp only [restrictedGraph, dif_pos hi]
      exact blockCommunication_get _ (hLabels i hi)
    · contradiction

section
variable {G Q : ProcessGraph schema}
variable (labels : ∀ i ∈ G.nodes, blockCommunication (G.label i) = some (Q.label i))

include labels in
private theorem blockStep_forward {src dst : GConfig schema} {a : Action schema}
    (hStep : GStep G src a dst) (allowed : actionAllowed Set.univ a) :
    ∀ {q}, blockCommunication src.proc = some q → gprocRefs src.proc ⊆ G.nodes →
      ∃ q', blockCommunication dst.proc = some q' ∧ gprocRefs dst.proc ⊆ G.nodes ∧
        GStep Q ⟨q, src.pending, src.handled⟩ a ⟨q', dst.pending, dst.handled⟩ := by
  induction hStep with
  | seq_ok N p σ τ pt hl sem =>
      intro q h hc
      have enabled : netkatIsZero N ≠ true := by
        intro zero
        exact (netkatIsZero_correct _).mp zero _ _
          ((historySemantics_singleton_iff_packetSemantics ..).mp sem)
      rw [blockCommunication, if_neg enabled] at h
      obtain ⟨q', hq, rfl⟩ := Option.map_eq_some'.mp h
      exact ⟨q', hq, hc, .seq_ok N q' σ τ pt hl sem⟩
  | rcfg x N p pt hl =>
      intro q h hc
      obtain ⟨q', hq, rfl⟩ := Option.map_eq_some'.mp h
      exact ⟨q', hq, hc, .rcfg x N q' pt hl⟩
  | choice_l p r p' a pt pt' hl hl' _ ih =>
      intro q h hc
      obtain ⟨s, hs, hr⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨t, _, rfl⟩ := Option.map_eq_some'.mp hr
      obtain ⟨s', h, hc', step⟩ := ih allowed hs (Finset.union_subset_iff.mp hc).1
      exact ⟨s', h, hc', .choice_l s t s' a pt pt' hl hl' step⟩
  | choice_r p r r' a pt pt' hl hl' _ ih =>
      intro q h hc
      obtain ⟨s, _, hr⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some'.mp hr
      obtain ⟨t', h, hc', step⟩ := ih allowed ht (Finset.union_subset_iff.mp hc).2
      exact ⟨t', h, hc', .choice_r s t t' a pt pt' hl hl' step⟩
  | var i p' a pt pt' hl hl' _ ih =>
      intro q h hc
      cases h
      have hi := hc (Finset.mem_singleton_self i)
      obtain ⟨q', h, hc', step⟩ := ih allowed (labels i hi) (G.closed i hi)
      exact ⟨q', h, hc', .var i q' a pt pt' hl hl' step⟩
  | recv | send => simp [actionAllowed] at allowed
  | par_l | par_r | left_merge | comm_merge_recv_send | comm_merge_send_recv |
    sync_recv_send | sync_send_recv | restrict | project =>
      intro _ h
      cases h

include labels in
private theorem blockStep_backward {src dst : GConfig schema} {a : Action schema}
    (hStep : GStep Q src a dst) :
    ∀ {p}, blockCommunication p = some src.proc → gprocRefs p ⊆ G.nodes →
      ∃ p', blockCommunication p' = some dst.proc ∧ gprocRefs p' ⊆ G.nodes ∧
        actionAllowed Set.univ a ∧
        GStep G ⟨p, src.pending, src.handled⟩ a ⟨p', dst.pending, dst.handled⟩ := by
  induction hStep with
  | seq_ok N q σ τ pt hl sem =>
      intro p hp hc
      cases p <;> try (simp [blockCommunication, Option.map_eq_some', Option.bind_eq_some_iff] at hp; done)
      rename_i pol cont
      rw [blockCommunication] at hp
      split at hp
      · cases hp
      · obtain ⟨t, ht, he⟩ := Option.map_eq_some'.mp hp
        cases he
        exact ⟨cont, ht, hc, trivial, .seq_ok _ _ σ τ pt hl sem⟩
  | rcfg x N q pt hl =>
      intro p hp hc
      cases p <;> try (simp [blockCommunication, Option.map_eq_some', Option.bind_eq_some_iff, ite_eq_iff'] at hp; done)
      rename_i chan pol cont
      obtain ⟨t, ht, he⟩ := Option.map_eq_some'.mp hp
      cases he
      exact ⟨cont, ht, hc, trivial, .rcfg _ _ _ pt hl⟩
  | choice_l q r q' a pt pt' hl hl' _ ih =>
      intro p hp hc
      cases p <;> try (simp [blockCommunication, Option.map_eq_some', Option.bind_eq_some_iff, ite_eq_iff'] at hp; done)
      rename_i u v
      obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.mp hp
      obtain ⟨t, ht, he⟩ := Option.map_eq_some'.mp h
      cases he
      obtain ⟨u', h, hc', ha, step⟩ := ih hs (Finset.union_subset_iff.mp hc).1
      exact ⟨u', h, hc', ha, .choice_l u v u' a pt pt' hl hl' step⟩
  | choice_r q r r' a pt pt' hl hl' _ ih =>
      intro p hp hc
      cases p <;> try (simp [blockCommunication, Option.map_eq_some', Option.bind_eq_some_iff, ite_eq_iff'] at hp; done)
      rename_i u v
      obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.mp hp
      obtain ⟨t, ht, he⟩ := Option.map_eq_some'.mp h
      cases he
      obtain ⟨v', h, hc', ha, step⟩ := ih ht (Finset.union_subset_iff.mp hc).2
      exact ⟨v', h, hc', ha, .choice_r u v v' a pt pt' hl hl' step⟩
  | var i q' a pt pt' hl hl' _ ih =>
      intro p hp hc
      cases p <;> simp [blockCommunication, Option.map_eq_some', Option.bind_eq_some_iff, ite_eq_iff'] at hp
      subst i
      have hi := hc (Finset.mem_singleton_self _)
      obtain ⟨p', h, hc', ha, step⟩ := ih (labels _ hi) (G.closed _ hi)
      exact ⟨p', h, hc', ha, .var _ p' a pt pt' hl hl' step⟩
  | recv | send | par_l | par_r | left_merge | comm_merge_recv_send | comm_merge_send_recv |
    sync_recv_send | sync_send_recv | restrict | project =>
      intro p hp
      cases p <;> simp [blockCommunication, Option.map_eq_some', Option.bind_eq_some_iff, ite_eq_iff'] at hp

end

/-- The relation pairing a closed original term under restriction with its
    translated term matches transitions in both directions. The derivative
    pairs satisfy the same relation, so the result applies at arbitrary depth. -/
theorem preprocessGraph_bisimulation {G Q : ProcessGraph schema}
    (h : preprocessGraph G = some Q) {p q : GProc schema}
    (hp : blockCommunication p = some q) (hc : gprocRefs p ⊆ G.nodes)
    (pt hl pt' hl' : List schema.Packet) (a : Action schema) :
    (∀ p', GStep G ⟨.restrict Set.univ p, pt, hl⟩ a ⟨.restrict Set.univ p', pt', hl'⟩ →
      ∃ q', blockCommunication p' = some q' ∧ gprocRefs p' ⊆ G.nodes ∧
        GStep Q ⟨q, pt, hl⟩ a ⟨q', pt', hl'⟩) ∧
    (∀ q', GStep Q ⟨q, pt, hl⟩ a ⟨q', pt', hl'⟩ →
      ∃ p', blockCommunication p' = some q' ∧ gprocRefs p' ⊆ G.nodes ∧
        GStep G ⟨.restrict Set.univ p, pt, hl⟩ a ⟨.restrict Set.univ p', pt', hl'⟩) := by
  have labels := (preprocessGraph_eq_some h).2.2
  constructor
  · intro p' step
    cases step with
    | restrict _ _ _ _ _ _ _ _ allowed step => exact blockStep_forward labels step allowed hp hc
  · intro q' step
    obtain ⟨p', hq, hc', ha, hstep⟩ := blockStep_backward labels step hp hc
    exact ⟨p', hq, hc', .restrict Set.univ p p' a pt pt' hl hl' ha hstep⟩

theorem preprocessGraph_exists {G : ProcessGraph schema}
    (root : (blockCommunication G.root).isSome)
    (labels : ∀ i ∈ G.nodes, (blockCommunication (G.label i)).isSome) :
    ∃ Q, preprocessGraph G = some Q := by
  unfold preprocessGraph
  split
  · rename_i eq
    simp [eq] at root
  · rw [dif_pos labels]
    exact ⟨_, rfl⟩

end DyNetKAT.DyNetKAT
