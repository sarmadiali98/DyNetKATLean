import DyNetKATLean.Core.ProcessGraph

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : NetKAT.PacketSchema}

open DyNetKAT.NetKAT

theorem GStep.rebase {G : ProcessGraph schema} {c d : GConfig schema} {a : Action schema}
    (h : GStep G c a d) (pt hl : List schema.Packet) :
    GStep G ⟨c.proc, a.pendingFor pt, hl⟩ a ⟨d.proc, pt, a.handledAfter hl⟩ := by
  induction h with
  | seq_ok N p σ τ _ _ h => exact .seq_ok N p σ τ pt hl h
  | recv => exact .recv _ _ _ pt hl
  | send => exact .send _ _ _ pt hl
  | rcfg => exact .rcfg _ _ _ pt hl
  | choice_l _ _ _ _ _ _ _ _ _ ih => exact .choice_l _ _ _ _ _ _ _ _ ih
  | choice_r _ _ _ _ _ _ _ _ _ ih => exact .choice_r _ _ _ _ _ _ _ _ ih
  | par_l _ _ _ _ _ _ _ _ _ ih => exact .par_l _ _ _ _ _ _ _ _ ih
  | par_r _ _ _ _ _ _ _ _ _ ih => exact .par_r _ _ _ _ _ _ _ _ ih
  | left_merge _ _ _ _ _ _ _ _ _ ih => exact .left_merge _ _ _ _ _ _ _ _ ih
  | comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .comm_merge_recv_send _ _ _ _ _ _ pt hl ih₁ ih₂
  | comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .comm_merge_send_recv _ _ _ _ _ _ pt hl ih₁ ih₂
  | sync_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .sync_recv_send _ _ _ _ _ _ pt hl ih₁ ih₂
  | sync_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .sync_send_recv _ _ _ _ _ _ pt hl ih₁ ih₂
  | var _ _ _ _ _ _ _ _ ih => exact .var _ _ _ _ _ _ _ ih
  | project _ _ _ _ _ _ _ _ _ ih => exact .project _ _ _ _ _ _ _ _ ih
  | restrict _ _ _ _ _ _ _ _ ha _ ih => exact .restrict _ _ _ _ _ _ _ _ ha ih

theorem GSteps.rebase {G : ProcessGraph schema} {c d : GConfig schema} {w : List (Action schema)}
    (h : GSteps G c w d) (pending handled : List schema.Packet) :
    GSteps G ⟨c.proc, w.foldr Action.pendingFor pending, handled⟩ w
      ⟨d.proc, pending, w.foldl (fun hl a => a.handledAfter hl) handled⟩ := by
  induction h generalizing handled with
  | nil => exact .nil _
  | cons _ _ _ _ _ step _ ih => exact .cons _ _ _ _ _ (step.rebase _ _) (ih _)

def GraphPath (G : ProcessGraph schema) (p : GProc schema) (w : List (Action schema)) (q : GProc schema) : Prop :=
  GSteps G ⟨p, w.foldr Action.pendingFor [], []⟩ w
    ⟨q, [], w.foldl (fun hl a => a.handledAfter hl) []⟩

def GraphActionStep (G : ProcessGraph schema) (p : GProc schema) (a : Action schema) (q : GProc schema) : Prop :=
  GStep G ⟨p, a.pendingFor [], []⟩ a ⟨q, [], a.handledAfter []⟩

theorem GraphPath.nil_iff {G : ProcessGraph schema} {p q : GProc schema} :
    GraphPath G p [] q ↔ p = q := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

theorem GraphPath.cons_iff {G : ProcessGraph schema} {p q : GProc schema} {a : Action schema} {w : List (Action schema)} :
    GraphPath G p (a :: w) q ↔ ∃ r, GraphActionStep G p a r ∧ GraphPath G r w q := by
  constructor
  · intro h
    cases h with
    | cons _ mid _ _ _ first rest => exact ⟨mid.proc, first.rebase [] [], rest.rebase [] []⟩
  · rintro ⟨r, first, rest⟩
    exact .cons _ _ _ _ _ (first.rebase _ _) (rest.rebase [] _)

theorem GraphPath.append_iff {G : ProcessGraph schema} {p q : GProc schema} {u v : List (Action schema)} :
    GraphPath G p (u ++ v) q ↔ ∃ r, GraphPath G p u r ∧ GraphPath G r v q := by
  induction u generalizing p with
  | nil => simp [nil_iff]
  | cons a u ih =>
      simp only [List.cons_append, cons_iff, ih]
      aesop

/-- Labels outside the original closed region do not influence its steps. -/
theorem GStep.of_agree {G Q : ProcessGraph schema} {nodes : Finset NodeId}
    (closed : ∀ i ∈ nodes, gprocRefs (G.label i) ⊆ nodes)
    (agree : ∀ i ∈ nodes, G.label i = Q.label i)
    {c d : GConfig schema} {a : Action schema} (h : GStep G c a d)
    (hc : gprocRefs c.proc ⊆ nodes) : GStep Q c a d := by
  induction h with
  | seq_ok _ _ _ _ _ _ ev => exact .seq_ok _ _ _ _ _ _ ev
  | recv => exact .recv _ _ _ _ _
  | send => exact .send _ _ _ _ _
  | rcfg => exact .rcfg _ _ _ _ _
  | choice_l _ _ _ _ _ _ _ _ _ ih => exact .choice_l _ _ _ _ _ _ _ _ (ih (Finset.union_subset_iff.mp hc).1)
  | choice_r _ _ _ _ _ _ _ _ _ ih => exact .choice_r _ _ _ _ _ _ _ _ (ih (Finset.union_subset_iff.mp hc).2)
  | par_l _ _ _ _ _ _ _ _ _ ih => exact .par_l _ _ _ _ _ _ _ _ (ih (Finset.union_subset_iff.mp hc).1)
  | par_r _ _ _ _ _ _ _ _ _ ih => exact .par_r _ _ _ _ _ _ _ _ (ih (Finset.union_subset_iff.mp hc).2)
  | left_merge _ _ _ _ _ _ _ _ _ ih => exact .left_merge _ _ _ _ _ _ _ _ (ih (Finset.union_subset_iff.mp hc).1)
  | comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .comm_merge_recv_send _ _ _ _ _ _ _ _ (ih₁ (Finset.union_subset_iff.mp hc).1)
        (ih₂ (Finset.union_subset_iff.mp hc).2)
  | comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .comm_merge_send_recv _ _ _ _ _ _ _ _ (ih₁ (Finset.union_subset_iff.mp hc).1)
        (ih₂ (Finset.union_subset_iff.mp hc).2)
  | sync_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .sync_recv_send _ _ _ _ _ _ _ _ (ih₁ (Finset.union_subset_iff.mp hc).1)
        (ih₂ (Finset.union_subset_iff.mp hc).2)
  | sync_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact .sync_send_recv _ _ _ _ _ _ _ _ (ih₁ (Finset.union_subset_iff.mp hc).1)
        (ih₂ (Finset.union_subset_iff.mp hc).2)
  | var i _ _ _ _ _ _ _ ih =>
      have hi := hc (Finset.mem_singleton_self i)
      exact .var _ _ _ _ _ _ _ (by rw [← agree i hi]; exact ih (closed i hi))
  | project _ _ _ _ _ _ _ _ _ ih => exact .project _ _ _ _ _ _ _ _ (ih hc)
  | restrict _ _ _ _ _ _ _ _ allowed _ ih => exact .restrict _ _ _ _ _ _ _ _ allowed (ih hc)

theorem GraphPath.agree {G Q : ProcessGraph schema} (labels : ∀ i ∈ G.nodes, Q.label i = G.label i)
    {p q : GProc schema} {w : List (Action schema)} (hc : gprocRefs p ⊆ G.nodes) :
    GraphPath Q p w q ↔ GraphPath G p w q := by
  have closed : ∀ i ∈ G.nodes, gprocRefs (Q.label i) ⊆ G.nodes := by
    intro i hi; rw [labels i hi]; exact G.closed i hi
  induction w generalizing p with
  | nil => simp only [nil_iff]
  | cons a w ih =>
      simp only [cons_iff]
      constructor
      · rintro ⟨r, step, rest⟩
        have first := GStep.of_agree closed labels step hc
        exact ⟨r, first, (ih (first.closed hc)).mp rest⟩
      · rintro ⟨r, step, rest⟩
        exact ⟨r, GStep.of_agree G.closed (fun i hi => (labels i hi).symm) step hc,
          (ih (step.closed hc)).mpr rest⟩

end DyNetKAT.DyNetKAT
