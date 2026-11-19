import DyNetKAT.DyNetKAT.GraphPaths
import DyNetKAT.DyNetKAT.GraphHead
import DyNetKAT.DyNetKAT.TailExtraction

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

/-- Packet pairs contributed by prefixes whose preceding reconfiguration events
    all belong to `R`. References follow graph labels, and each witness is a
    finite derivation ending at a packet prefix. -/
inductive GraphAllRSpec (G : ProcessGraph) (R : ReconfigSet) :
    GProc → CtxPkt → CtxPkt → Prop
  | nSeq_of_sem (N : NetKAT) (cont : GProc) (σ τ : CtxPkt)
      (h : Semantics N σ τ) : GraphAllRSpec G R (.nSeq N cont) σ τ
  | nSeq_of (N : NetKAT) (cont : GProc) (σ τ : CtxPkt)
      (h : GraphAllRSpec G R cont σ τ) : GraphAllRSpec G R (.nSeq N cont) σ τ
  | choice_left (a b : GProc) (σ τ : CtxPkt)
      (h : GraphAllRSpec G R a σ τ) : GraphAllRSpec G R (.choice a b) σ τ
  | choice_right (a b : GProc) (σ τ : CtxPkt)
      (h : GraphAllRSpec G R b σ τ) : GraphAllRSpec G R (.choice a b) σ τ
  | rcfgPrefix_of (x : Channel) (N : NetKAT) (cont : GProc) (σ τ : CtxPkt)
      (hmem : (x, N) ∈ R) (h : GraphAllRSpec G R cont σ τ) :
      GraphAllRSpec G R (.rcfgPrefix x N cont) σ τ
  | ref_of (i : NodeId) (σ τ : CtxPkt)
      (h : GraphAllRSpec G R (G.label i) σ τ) : GraphAllRSpec G R (.ref i) σ τ

/-- Packet pairs contributed after at least one reconfiguration, with every
    preceding reconfiguration event in `R`. The first match discharges the
    requirement to cross a reconfiguration and leaves the all-R obligation. -/
inductive GraphTailSpec (G : ProcessGraph) (R : ReconfigSet) :
    GProc → CtxPkt → CtxPkt → Prop
  | nSeq_of (N : NetKAT) (cont : GProc) (σ τ : CtxPkt)
      (h : GraphTailSpec G R cont σ τ) : GraphTailSpec G R (.nSeq N cont) σ τ
  | choice_left (a b : GProc) (σ τ : CtxPkt)
      (h : GraphTailSpec G R a σ τ) : GraphTailSpec G R (.choice a b) σ τ
  | choice_right (a b : GProc) (σ τ : CtxPkt)
      (h : GraphTailSpec G R b σ τ) : GraphTailSpec G R (.choice a b) σ τ
  | rcfgPrefix_of (x : Channel) (N : NetKAT) (cont : GProc) (σ τ : CtxPkt)
      (hmem : (x, N) ∈ R) (h : GraphAllRSpec G R cont σ τ) :
      GraphTailSpec G R (.rcfgPrefix x N cont) σ τ
  | ref_of (i : NodeId) (σ τ : CtxPkt)
      (h : GraphTailSpec G R (G.label i) σ τ) : GraphTailSpec G R (.ref i) σ τ

variable {G : ProcessGraph} {R : ReconfigSet} {gp : GProc} {σ τ : CtxPkt}

theorem graphAllRSpec_nSeq_iff (N : NetKAT) (cont : GProc) :
    GraphAllRSpec G R (.nSeq N cont) σ τ ↔
      Semantics N σ τ ∨ GraphAllRSpec G R cont σ τ := by
  constructor
  · intro h
    cases h with
    | nSeq_of_sem _ _ _ _ hsem => exact Or.inl hsem
    | nSeq_of _ _ _ _ hcont => exact Or.inr hcont
  · rintro (hsem | hcont)
    · exact .nSeq_of_sem N cont σ τ hsem
    · exact .nSeq_of N cont σ τ hcont

theorem graphAllRSpec_choice_iff (a b : GProc) :
    GraphAllRSpec G R (.choice a b) σ τ ↔
      GraphAllRSpec G R a σ τ ∨ GraphAllRSpec G R b σ τ := by
  constructor
  · intro h
    cases h with
    | choice_left _ _ _ _ ha => exact Or.inl ha
    | choice_right _ _ _ _ hb => exact Or.inr hb
  · rintro (ha | hb)
    · exact .choice_left a b σ τ ha
    · exact .choice_right a b σ τ hb

theorem graphAllRSpec_rcfgPrefix_iff (x : Channel) (N : NetKAT) (cont : GProc) :
    GraphAllRSpec G R (.rcfgPrefix x N cont) σ τ ↔
      (x, N) ∈ R ∧ GraphAllRSpec G R cont σ τ := by
  constructor
  · intro h
    cases h with
    | rcfgPrefix_of _ _ _ _ _ hmem hcont => exact ⟨hmem, hcont⟩
  · rintro ⟨hmem, hcont⟩
    exact .rcfgPrefix_of x N cont σ τ hmem hcont

theorem graphAllRSpec_ref_iff (i : NodeId) :
    GraphAllRSpec G R (.ref i) σ τ ↔ GraphAllRSpec G R (G.label i) σ τ := by
  constructor
  · intro h
    cases h with
    | ref_of _ _ _ hlabel => exact hlabel
  · exact GraphAllRSpec.ref_of i σ τ

theorem graphTailSpec_nSeq_iff (N : NetKAT) (cont : GProc) :
    GraphTailSpec G R (.nSeq N cont) σ τ ↔ GraphTailSpec G R cont σ τ := by
  constructor
  · intro h
    cases h with
    | nSeq_of _ _ _ _ hcont => exact hcont
  · exact GraphTailSpec.nSeq_of N cont σ τ

theorem graphTailSpec_choice_iff (a b : GProc) :
    GraphTailSpec G R (.choice a b) σ τ ↔
      GraphTailSpec G R a σ τ ∨ GraphTailSpec G R b σ τ := by
  constructor
  · intro h
    cases h with
    | choice_left _ _ _ _ ha => exact Or.inl ha
    | choice_right _ _ _ _ hb => exact Or.inr hb
  · rintro (ha | hb)
    · exact .choice_left a b σ τ ha
    · exact .choice_right a b σ τ hb

theorem graphTailSpec_rcfgPrefix_iff (x : Channel) (N : NetKAT) (cont : GProc) :
    GraphTailSpec G R (.rcfgPrefix x N cont) σ τ ↔
      (x, N) ∈ R ∧ GraphAllRSpec G R cont σ τ := by
  constructor
  · intro h
    cases h with
    | rcfgPrefix_of _ _ _ _ _ hmem hcont => exact ⟨hmem, hcont⟩
  · rintro ⟨hmem, hcont⟩
    exact .rcfgPrefix_of x N cont σ τ hmem hcont

theorem graphTailSpec_ref_iff (i : NodeId) :
    GraphTailSpec G R (.ref i) σ τ ↔ GraphTailSpec G R (G.label i) σ τ := by
  constructor
  · intro h
    cases h with
    | ref_of _ _ _ hlabel => exact hlabel
  · exact GraphTailSpec.ref_of i σ τ

theorem graphAllRSpec_deadlock_false : ¬ GraphAllRSpec G R .deadlock σ τ := by
  intro h
  cases h

theorem graphTailSpec_deadlock_false : ¬ GraphTailSpec G R .deadlock σ τ := by
  intro h
  cases h

/-- The same seven outer constructors excluded by graph head have no all-R
    derivation. -/
theorem graphAllRSpec_unsupported_false (h : HeadUnsupported gp) :
    ¬ GraphAllRSpec G R gp σ τ := by
  cases h <;> intro hspec <;> cases hspec

theorem graphTailSpec_unsupported_false (h : HeadUnsupported gp) :
    ¬ GraphTailSpec G R gp σ τ := by
  cases h <;> intro hspec <;> cases hspec

/-- Split an all-R derivation at its first matching reconfiguration, if any. -/
theorem allR_split (h : GraphAllRSpec G R gp σ τ) :
    GraphHeadSpec G gp σ τ ∨ GraphTailSpec G R gp σ τ := by
  induction h with
  | nSeq_of_sem N cont σ τ hsem =>
      exact Or.inl (.nSeq_of_sem N cont σ τ hsem)
  | nSeq_of N cont σ τ _ ih =>
      rcases ih with hhead | htail
      · exact Or.inl (.nSeq_of_tail N cont σ τ hhead)
      · exact Or.inr (.nSeq_of N cont σ τ htail)
  | choice_left a b σ τ _ ih =>
      rcases ih with hhead | htail
      · exact Or.inl (.choice_left a b σ τ hhead)
      · exact Or.inr (.choice_left a b σ τ htail)
  | choice_right a b σ τ _ ih =>
      rcases ih with hhead | htail
      · exact Or.inl (.choice_right a b σ τ hhead)
      · exact Or.inr (.choice_right a b σ τ htail)
  | rcfgPrefix_of x N cont σ τ hmem hcont _ =>
      exact Or.inr (.rcfgPrefix_of x N cont σ τ hmem hcont)
  | ref_of i σ τ _ ih =>
      rcases ih with hhead | htail
      · exact Or.inl (.ref_of i σ τ hhead)
      · exact Or.inr (.ref_of i σ τ htail)

theorem head_in_allR (h : GraphHeadSpec G gp σ τ) : GraphAllRSpec G R gp σ τ := by
  induction h with
  | nSeq_of_sem N cont σ τ hsem => exact .nSeq_of_sem N cont σ τ hsem
  | nSeq_of_tail N cont σ τ _ ih => exact .nSeq_of N cont σ τ ih
  | choice_left a b σ τ _ ih => exact .choice_left a b σ τ ih
  | choice_right a b σ τ _ ih => exact .choice_right a b σ τ ih
  | ref_of i σ τ _ ih => exact .ref_of i σ τ ih

theorem tail_in_allR (h : GraphTailSpec G R gp σ τ) : GraphAllRSpec G R gp σ τ := by
  induction h with
  | nSeq_of N cont σ τ _ ih => exact .nSeq_of N cont σ τ ih
  | choice_left a b σ τ _ ih => exact .choice_left a b σ τ ih
  | choice_right a b σ τ _ ih => exact .choice_right a b σ τ ih
  | rcfgPrefix_of x N cont σ τ hmem hcont => exact .rcfgPrefix_of x N cont σ τ hmem hcont
  | ref_of i σ τ _ ih => exact .ref_of i σ τ ih

theorem graphAllR_iff_head_or_tail :
    GraphAllRSpec G R gp σ τ ↔ GraphHeadSpec G gp σ τ ∨ GraphTailSpec G R gp σ τ := by
  refine ⟨allR_split, ?_⟩
  rintro (hhead | htail)
  · exact head_in_allR hhead
  · exact tail_in_allR htail

/-- On a variable-free AST, the graph translation has the same all-R relation
    for every choice of graph labels. -/
theorem graphAllRSpec_toGProc_iff (d : DyNetKAT) (hfree : recursiveVars d = ∅) :
    GraphAllRSpec G R (toGProc d) σ τ ↔ AllRSpec R d σ τ := by
  induction d with
  | deadlock =>
      simp [toGProc, graphAllRSpec_deadlock_false, allRSpec_deadlock_false]
  | nSeq N cont ih =>
      rw [toGProc, graphAllRSpec_nSeq_iff, allRSpec_nSeq_iff, ih hfree]
  | choice a b iha ihb =>
      obtain ⟨ha, hb⟩ := Finset.union_eq_empty.mp hfree
      rw [toGProc, graphAllRSpec_choice_iff, allRSpec_choice_iff, iha ha, ihb hb]
  | rcfgPrefix x N cont ih =>
      rw [toGProc, graphAllRSpec_rcfgPrefix_iff, allRSpec_rcfgPrefix_iff, ih hfree]
  | var x => simp [recursiveVars] at hfree
  | recv | send | parallel | leftMerge | commMerge | restrict | project =>
      rw [toGProc]
      constructor <;> intro h <;> cases h

/-- On a variable-free AST, graph-tail and AST tail-head specifications agree. -/
theorem graphTailSpec_toGProc_iff (d : DyNetKAT) (hfree : recursiveVars d = ∅) :
    GraphTailSpec G R (toGProc d) σ τ ↔ TailHeadSpec R d σ τ := by
  induction d with
  | deadlock =>
      simp [toGProc, graphTailSpec_deadlock_false, tailHeadSpec_deadlock_false]
  | nSeq N cont ih =>
      rw [toGProc, graphTailSpec_nSeq_iff, tailHeadSpec_nSeq_iff, ih hfree]
  | choice a b iha ihb =>
      obtain ⟨ha, hb⟩ := Finset.union_eq_empty.mp hfree
      rw [toGProc, graphTailSpec_choice_iff, tailHeadSpec_choice_iff, iha ha, ihb hb]
  | rcfgPrefix x N cont _ =>
      rw [toGProc, graphTailSpec_rcfgPrefix_iff, tailHeadSpec_rcfgPrefix_iff,
        graphAllRSpec_toGProc_iff cont hfree]
  | var x => simp [recursiveVars] at hfree
  | recv | send | parallel | leftMerge | commMerge | restrict | project =>
      rw [toGProc]
      constructor <;> intro h <;> cases h

/-! ## R-visible reference discovery and reachability -/

/-- List the references exposed by a term, in left-to-right order. Labels
    are inspected separately by the worklist. -/
def tailRefsR (R : ReconfigSet) : GProc → List NodeId
  | .deadlock => []
  | .nSeq _ cont => tailRefsR R cont
  | .choice a b => tailRefsR R a ++ tailRefsR R b
  | .rcfgPrefix x N cont => if (x, N) ∈ R then tailRefsR R cont else []
  | .ref i => [i]
  | _ => []

/-- A reference at an R-visible position of a single term. -/
inductive TailRefOf (R : ReconfigSet) : GProc → NodeId → Prop
  | ref (i : NodeId) : TailRefOf R (.ref i) i
  | nSeq {N cont i} : TailRefOf R cont i → TailRefOf R (.nSeq N cont) i
  | choice_left {a b i} : TailRefOf R a i → TailRefOf R (.choice a b) i
  | choice_right {a b i} : TailRefOf R b i → TailRefOf R (.choice a b) i
  | rcfgPrefix {x N cont i} :
      (x, N) ∈ R → TailRefOf R cont i → TailRefOf R (.rcfgPrefix x N cont) i

theorem mem_tailRefsR_iff (R : ReconfigSet) (gp : GProc) (i : NodeId) :
    i ∈ tailRefsR R gp ↔ TailRefOf R gp i := by
  constructor
  · induction gp with
    | ref j =>
        intro h
        have hij : i = j := by simpa [tailRefsR] using h
        subst i
        exact .ref j
    | nSeq N cont ih =>
        intro h
        exact .nSeq (ih h)
    | choice a b iha ihb =>
        intro h
        rcases List.mem_append.mp h with ha | hb
        · exact .choice_left (iha ha)
        · exact .choice_right (ihb hb)
    | rcfgPrefix x N cont ih =>
        by_cases hmem : (x, N) ∈ R
        · intro h
          exact .rcfgPrefix hmem (ih (by simpa [tailRefsR, hmem] using h))
        · simp [tailRefsR, hmem]
    | deadlock | recv | send | parallel | leftMerge | commMerge | restrict | project =>
        simp [tailRefsR]
  · intro h
    induction h with
    | ref j => simp [tailRefsR]
    | nSeq _ ih => exact ih
    | choice_left _ ih => exact List.mem_append_left _ ih
    | choice_right _ ih => exact List.mem_append_right _ ih
    | rcfgPrefix hmem _ ih => simpa [tailRefsR, hmem] using ih

theorem tailRefsR_subset_gprocRefs (R : ReconfigSet) (gp : GProc) {i : NodeId}
    (hi : i ∈ tailRefsR R gp) : i ∈ gprocRefs gp := by
  have h := (mem_tailRefsR_iff R gp i).mp hi
  clear hi
  induction h with
  | ref j => simp [gprocRefs]
  | nSeq _ ih | rcfgPrefix _ _ ih => exact ih
  | choice_left _ ih => exact Finset.mem_union_left _ ih
  | choice_right _ ih => exact Finset.mem_union_right _ ih

/-- Finite node paths along the R-visible references of node labels. -/
inductive TailRefReach (G : ProcessGraph) (R : ReconfigSet) : NodeId → NodeId → Prop
  | refl (i : NodeId) : TailRefReach G R i i
  | step {i v j} : v ∈ tailRefsR R (G.label i) →
      TailRefReach G R v j → TailRefReach G R i j

/-- A path from a process first finds an R-visible reference in the term
    and then follows a finite node path. -/
def TailPathTo (G : ProcessGraph) (R : ReconfigSet) (gp : GProc) (j : NodeId) : Prop :=
  ∃ i, TailRefOf R gp i ∧ TailRefReach G R i j

theorem tailPathTo_iff (G : ProcessGraph) (R : ReconfigSet) (gp : GProc) (j : NodeId) :
    TailPathTo G R gp j ↔ ∃ i, i ∈ tailRefsR R gp ∧ TailRefReach G R i j := by
  simp only [TailPathTo, mem_tailRefsR_iff]

theorem tailRefReach_iff_tailPathTo (G : ProcessGraph) (R : ReconfigSet) (i j : NodeId) :
    TailRefReach G R i j ↔ TailPathTo G R (.ref i) j := by
  simp [tailPathTo_iff, tailRefsR]

/-- A direct reference of a reachable label is reachable from the same term. -/
theorem tailPathTo_step {j k : NodeId} (h : TailPathTo G R gp j)
    (hk : k ∈ tailRefsR R (G.label j)) : TailPathTo G R gp k := by
  obtain ⟨i, hi, hreach⟩ := h
  refine ⟨i, hi, ?_⟩
  clear hi
  induction hreach with
  | refl j => exact .step hk (.refl k)
  | step hv _ ih => exact .step hv (ih hk)

/-- The closure fields of a process graph cover every node reachable from
    its root by an R-visible path. -/
theorem tailPathTo_nodes_closed {j : NodeId} (h : TailPathTo G R G.root j) :
    j ∈ G.nodes := by
  obtain ⟨i, hi, hreach⟩ := (tailPathTo_iff G R G.root j).mp h
  have hiNode := G.root_closed (tailRefsR_subset_gprocRefs R G.root hi)
  clear h hi
  induction hreach with
  | refl i => exact hiNode
  | step hv _ ih =>
      exact ih (G.closed _ hiNode (tailRefsR_subset_gprocRefs R _ hv))

/-! ## Cycle-safe worklist -/

/-- Process pending references in order, recording visits by prepending
    to the accumulator. An unvisited reference outside the graph fails. -/
def tailRun (G : ProcessGraph) (R : ReconfigSet) :
    List NodeId → Finset NodeId → List NodeId → Option (List NodeId)
  | [], _, acc => some acc
  | i :: rest, visited, acc =>
      if _hVisited : i ∈ visited then tailRun G R rest visited acc
      else if _hNode : i ∈ G.nodes then
        tailRun G R (rest ++ tailRefsR R (G.label i)) (insert i visited) (i :: acc)
      else none
termination_by pending visited _ => ((G.nodes \ visited).card, pending.length)
decreasing_by
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  · have hmem : i ∈ G.nodes \ visited := Finset.mem_sdiff.mpr ⟨_hNode, _hVisited⟩
    apply Prod.Lex.left
    rw [Finset.sdiff_insert]
    exact Finset.card_erase_lt_of_mem hmem

private theorem tailRun_cover_visited (G : ProcessGraph) (R : ReconfigSet)
    (visited : Finset NodeId) (pending : List NodeId)
    (hExpanded : ∀ i ∈ visited, ∀ v ∈ tailRefsR R (G.label i), v ∈ visited ∨ v ∈ pending)
    {i j : NodeId} (h : TailRefReach G R i j) (hi : i ∈ visited) (hj : j ∉ visited) :
    ∃ v, v ∈ pending ∧ v ∉ visited ∧ TailRefReach G R v j := by
  induction h with
  | refl i => exact absurd hi hj
  | @step i v j hv hreach ih =>
      rcases hExpanded _ hi _ hv with hvVisited | hvPending
      · exact ih hvVisited hj
      · by_cases hvVisited : v ∈ visited
        · exact ih hvVisited hj
        · exact ⟨_, hvPending, hvVisited, hreach⟩

/-- The visited set contains only live, root-reachable nodes. The accumulator
    lists exactly those nodes once. The pending list accounts for every
    reachable node still to visit and every outstanding edge of a visited node. -/
theorem tailRun_spec (G : ProcessGraph) (R : ReconfigSet) (pending : List NodeId)
    (visited : Finset NodeId) (acc : List NodeId)
    (hVisited : ∀ i ∈ visited, TailPathTo G R G.root i ∧ i ∈ G.nodes)
    (hAcc : ∀ i, i ∈ acc ↔ i ∈ visited)
    (hNodup : acc.Nodup)
    (hPending : ∀ i ∈ pending, TailPathTo G R G.root i)
    (hCover : ∀ j, TailPathTo G R G.root j →
      j ∈ visited ∨ ∃ i, i ∈ pending ∧ TailRefReach G R i j)
    (hExpanded : ∀ i ∈ visited, ∀ v ∈ tailRefsR R (G.label i), v ∈ visited ∨ v ∈ pending) :
    (tailRun G R pending visited acc = none →
      ∃ j, TailPathTo G R G.root j ∧ j ∉ G.nodes) ∧
    (∀ L, tailRun G R pending visited acc = some L →
      L.Nodup ∧ (∀ j, j ∈ L ↔ TailPathTo G R G.root j) ∧ ∀ j ∈ L, j ∈ G.nodes) := by
  fun_induction tailRun G R pending visited acc
  case case1 visited acc =>
    rw [tailRun.eq_1]
    refine ⟨fun h => Option.noConfusion h, ?_⟩
    intro L hL
    cases hL
    refine ⟨hNodup, fun j => ⟨?_, ?_⟩, ?_⟩
    · intro hj
      exact (hVisited j ((hAcc j).mp hj)).1
    · intro hj
      rcases hCover j hj with hjVisited | ⟨i, hi, _⟩
      · exact (hAcc j).mpr hjVisited
      · simp at hi
    · exact fun j hj => (hVisited j ((hAcc j).mp hj)).2
  case case2 i rest visited acc hi ih =>
    have hPending' : ∀ k ∈ rest, TailPathTo G R G.root k :=
      fun k hk => hPending k (List.mem_cons_of_mem _ hk)
    have hExpanded' : ∀ k ∈ visited, ∀ v ∈ tailRefsR R (G.label k),
        v ∈ visited ∨ v ∈ rest := by
      intro k hk v hv
      rcases hExpanded k hk v hv with hvVisited | hvPending
      · exact Or.inl hvVisited
      · rcases List.mem_cons.mp hvPending with rfl | hvRest
        · exact Or.inl hi
        · exact Or.inr hvRest
    have hCover' : ∀ j, TailPathTo G R G.root j →
        j ∈ visited ∨ ∃ k, k ∈ rest ∧ TailRefReach G R k j := by
      intro j hj
      by_cases hjVisited : j ∈ visited
      · exact Or.inl hjVisited
      · rcases hCover j hj with hj' | ⟨k, hk, hreach⟩
        · exact absurd hj' hjVisited
        · rcases List.mem_cons.mp hk with rfl | hkRest
          · obtain ⟨v, hv, hvUnvisited, hvReach⟩ :=
              tailRun_cover_visited G R visited (k :: rest) hExpanded hreach hi hjVisited
            rcases List.mem_cons.mp hv with rfl | hvRest
            · exact absurd hi hvUnvisited
            · exact Or.inr ⟨v, hvRest, hvReach⟩
          · exact Or.inr ⟨k, hkRest, hreach⟩
    rw [tailRun.eq_2, dif_pos hi]
    exact ih hVisited hAcc hNodup hPending' hCover' hExpanded'
  case case3 i rest visited acc hi hiNode ih =>
    have hiPath := hPending i (List.Mem.head _)
    have hVisited' : ∀ k ∈ insert i visited, TailPathTo G R G.root k ∧ k ∈ G.nodes := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hkVisited
      · exact ⟨hiPath, hiNode⟩
      · exact hVisited k hkVisited
    have hAcc' : ∀ k, k ∈ i :: acc ↔ k ∈ insert i visited := by
      intro k
      simp only [List.mem_cons, Finset.mem_insert, hAcc]
    have hNodup' : (i :: acc).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hi ((hAcc i).mp h), hNodup⟩
    have hPending' : ∀ k ∈ rest ++ tailRefsR R (G.label i), TailPathTo G R G.root k := by
      intro k hk
      rcases List.mem_append.mp hk with hkRest | hkRef
      · exact hPending k (List.mem_cons_of_mem _ hkRest)
      · exact tailPathTo_step hiPath hkRef
    have hCover' : ∀ j, TailPathTo G R G.root j →
        j ∈ insert i visited ∨
          ∃ k, k ∈ rest ++ tailRefsR R (G.label i) ∧ TailRefReach G R k j := by
      intro j hj
      rcases hCover j hj with hjVisited | ⟨k, hk, hreach⟩
      · exact Or.inl (Finset.mem_insert_of_mem hjVisited)
      · rcases List.mem_cons.mp hk with rfl | hkRest
        · cases hreach with
          | refl => exact Or.inl (Finset.mem_insert_self _ _)
          | step hv hvReach => exact Or.inr ⟨_, List.mem_append_right _ hv, hvReach⟩
        · exact Or.inr ⟨k, List.mem_append_left _ hkRest, hreach⟩
    have hExpanded' : ∀ k ∈ insert i visited, ∀ v ∈ tailRefsR R (G.label k),
        v ∈ insert i visited ∨ v ∈ rest ++ tailRefsR R (G.label i) := by
      intro k hk v hv
      rcases Finset.mem_insert.mp hk with rfl | hkVisited
      · exact Or.inr (List.mem_append_right _ hv)
      · rcases hExpanded k hkVisited v hv with hvVisited | hvPending
        · exact Or.inl (Finset.mem_insert_of_mem hvVisited)
        · rcases List.mem_cons.mp hvPending with rfl | hvRest
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr (List.mem_append_left _ hvRest)
    rw [tailRun.eq_2, dif_neg hi, dif_pos hiNode]
    exact ih hVisited' hAcc' hNodup' hPending' hCover' hExpanded'
  case case4 i rest visited acc hi hiNode =>
    rw [tailRun.eq_2, dif_neg hi, dif_neg hiNode]
    exact ⟨fun _ => ⟨i, hPending i (List.Mem.head _), hiNode⟩,
      fun _ h => Option.noConfusion h⟩

private theorem tailRun_root_spec (G : ProcessGraph) (R : ReconfigSet) :
    (tailRun G R (tailRefsR R G.root) ∅ [] = none →
      ∃ j, TailPathTo G R G.root j ∧ j ∉ G.nodes) ∧
    (∀ L, tailRun G R (tailRefsR R G.root) ∅ [] = some L →
      L.Nodup ∧ (∀ j, j ∈ L ↔ TailPathTo G R G.root j) ∧ ∀ j ∈ L, j ∈ G.nodes) :=
  tailRun_spec G R (tailRefsR R G.root) ∅ []
    (by simp)
    (by simp)
    List.nodup_nil
    (fun i hi => (tailPathTo_iff G R G.root i).mpr ⟨i, hi, .refl i⟩)
    (fun j hj => Or.inr ((tailPathTo_iff G R G.root j).mp hj))
    (by simp)

theorem tailRun_root_success (G : ProcessGraph) (R : ReconfigSet) (L : List NodeId)
    (h : tailRun G R (tailRefsR R G.root) ∅ [] = some L) :
    L.Nodup ∧ (∀ j, j ∈ L ↔ TailPathTo G R G.root j) ∧ ∀ j ∈ L, j ∈ G.nodes :=
  (tailRun_root_spec G R).2 L h

theorem tailRun_root_failure (G : ProcessGraph) (R : ReconfigSet)
    (h : tailRun G R (tailRefsR R G.root) ∅ [] = none) :
    ∃ j, TailPathTo G R G.root j ∧ j ∉ G.nodes :=
  (tailRun_root_spec G R).1 h

theorem tailRun_root_some (G : ProcessGraph) (R : ReconfigSet) :
    ∃ L, tailRun G R (tailRefsR R G.root) ∅ [] = some L := by
  cases h : tailRun G R (tailRefsR R G.root) ∅ [] with
  | none =>
      obtain ⟨j, hj, hMissing⟩ := tailRun_root_failure G R h
      exact absurd (tailPathTo_nodes_closed hj) hMissing
  | some L => exact ⟨L, rfl⟩

/-! ## Local tail collection -/

/-- Collect a local tail without following graph labels. A matching event
    contributes its original continuation alongside the recursively collected
    tail. Only references reached by the collector are replaced. -/
def tailCollectR (G : ProcessGraph) (R : ReconfigSet)
    (fresh : NodeId → NodeId) : GProc → Option GProc
  | .deadlock => some .deadlock
  | .nSeq _ cont => tailCollectR G R fresh cont
  | .choice a b =>
      match tailCollectR G R fresh a, tailCollectR G R fresh b with
      | some a', some b' => some (.choice a' b')
      | _, _ => none
  | .rcfgPrefix x N cont =>
      if (x, N) ∈ R then
        match tailCollectR G R fresh cont with
        | some out => some (.choice cont out)
        | none => none
      else some .deadlock
  | .ref i => some (.ref (fresh i))
  | .recv _ _ _ => none
  | .send _ _ _ => none
  | .parallel _ _ => none
  | .leftMerge _ _ => none
  | .commMerge _ _ => none
  | .restrict _ _ => none
  | .project _ _ => none

section

variable {fresh : NodeId → NodeId}

@[simp] theorem tailCollectR_deadlock :
    tailCollectR G R fresh .deadlock = some .deadlock := rfl

@[simp] theorem tailCollectR_nSeq (N : NetKAT) (cont : GProc) :
    tailCollectR G R fresh (.nSeq N cont) = tailCollectR G R fresh cont := rfl

theorem tailCollectR_choice (a b : GProc) :
    tailCollectR G R fresh (.choice a b) =
      match tailCollectR G R fresh a, tailCollectR G R fresh b with
      | some a', some b' => some (.choice a' b')
      | _, _ => none := rfl

theorem tailCollectR_rcfgPrefix (x : Channel) (N : NetKAT) (cont : GProc) :
    tailCollectR G R fresh (.rcfgPrefix x N cont) =
      if (x, N) ∈ R then (tailCollectR G R fresh cont).map (.choice cont)
      else some .deadlock := by
  cases h : tailCollectR G R fresh cont <;> simp [tailCollectR, h]

@[simp] theorem tailCollectR_ref (i : NodeId) :
    tailCollectR G R fresh (.ref i) = some (.ref (fresh i)) := rfl

@[simp] theorem tailCollectR_recv (x : Channel) (N : NetKAT) (cont : GProc) :
    tailCollectR G R fresh (.recv x N cont) = none := rfl

@[simp] theorem tailCollectR_send (x : Channel) (N : NetKAT) (cont : GProc) :
    tailCollectR G R fresh (.send x N cont) = none := rfl

@[simp] theorem tailCollectR_parallel (a b : GProc) :
    tailCollectR G R fresh (.parallel a b) = none := rfl

@[simp] theorem tailCollectR_leftMerge (a b : GProc) :
    tailCollectR G R fresh (.leftMerge a b) = none := rfl

@[simp] theorem tailCollectR_commMerge (a b : GProc) :
    tailCollectR G R fresh (.commMerge a b) = none := rfl

@[simp] theorem tailCollectR_restrict (actions : Set CommunicationAction) (cont : GProc) :
    tailCollectR G R fresh (.restrict actions cont) = none := rfl

@[simp] theorem tailCollectR_project (n : Nat) (cont : GProc) :
    tailCollectR G R fresh (.project n cont) = none := rfl

theorem tailCollectR_choice_some_iff {a b out : GProc} :
    tailCollectR G R fresh (.choice a b) = some out ↔
      ∃ a' b', tailCollectR G R fresh a = some a' ∧
        tailCollectR G R fresh b = some b' ∧ out = .choice a' b' := by
  cases ha : tailCollectR G R fresh a <;> cases hb : tailCollectR G R fresh b <;>
    simp [tailCollectR_choice, ha, hb, eq_comm]

theorem tailCollectR_choice_none_iff {a b : GProc} :
    tailCollectR G R fresh (.choice a b) = none ↔
      tailCollectR G R fresh a = none ∨ tailCollectR G R fresh b = none := by
  cases ha : tailCollectR G R fresh a <;> cases hb : tailCollectR G R fresh b <;>
    simp [tailCollectR_choice, ha, hb]

theorem tailCollectR_rcfgPrefix_mem_some_iff {x : Channel} {N : NetKAT}
    {cont out : GProc} (hmem : (x, N) ∈ R) :
    tailCollectR G R fresh (.rcfgPrefix x N cont) = some out ↔
      ∃ tail, tailCollectR G R fresh cont = some tail ∧ out = .choice cont tail := by
  rw [tailCollectR_rcfgPrefix, if_pos hmem, Option.map_eq_some']
  simp only [eq_comm]

theorem tailCollectR_rcfgPrefix_mem_none_iff {x : Channel} {N : NetKAT}
    {cont : GProc} (hmem : (x, N) ∈ R) :
    tailCollectR G R fresh (.rcfgPrefix x N cont) = none ↔
      tailCollectR G R fresh cont = none := by
  simp [tailCollectR_rcfgPrefix, hmem]

@[simp] theorem tailCollectR_rcfgPrefix_not_mem {x : Channel} {N : NetKAT}
    (cont : GProc) (hmem : (x, N) ∉ R) :
    tailCollectR G R fresh (.rcfgPrefix x N cont) = some .deadlock := by
  simp [tailCollectR_rcfgPrefix, hmem]

/-- Shape of the outer constructor only. A verbatim branch of a choice can
    still contain packet prefixes and original references. -/
theorem tailCollectR_image_shape {out : GProc} (h : tailCollectR G R fresh gp = some out) :
    out = .deadlock ∨ (∃ a b, out = .choice a b) ∨ (∃ i, out = .ref (fresh i)) := by
  induction gp with
  | deadlock => exact Or.inl (Option.some.inj h).symm
  | nSeq N cont ih => exact ih h
  | choice a b =>
      obtain ⟨a', b', _, _, hout⟩ := tailCollectR_choice_some_iff.mp h
      exact Or.inr (Or.inl ⟨a', b', hout⟩)
  | rcfgPrefix x N cont =>
      by_cases hmem : (x, N) ∈ R
      · obtain ⟨tail, _, hout⟩ := (tailCollectR_rcfgPrefix_mem_some_iff hmem).mp h
        exact Or.inr (Or.inl ⟨cont, tail, hout⟩)
      · rw [tailCollectR_rcfgPrefix_not_mem cont hmem] at h
        exact Or.inl (Option.some.inj h).symm
  | ref i => exact Or.inr (Or.inr ⟨i, (Option.some.inj h).symm⟩)
  | recv | send | parallel | leftMerge | commMerge | restrict | project => simp at h

end

/-- A reference preceded by zero or more packet-processing prefixes. -/
inductive NSeqRefSpine : GProc → NodeId → Prop
  | ref (i : NodeId) : NSeqRefSpine (.ref i) i
  | nSeq {N : NetKAT} {cont : GProc} {i : NodeId} :
      NSeqRefSpine cont i → NSeqRefSpine (.nSeq N cont) i

theorem NSeqRefSpine.mem_tailRefsR {i : NodeId} (h : NSeqRefSpine gp i) :
    i ∈ tailRefsR R gp := by
  induction h with
  | ref i => simp [tailRefsR]
  | nSeq _ ih => exact ih

section

variable {fresh : NodeId → NodeId}

/-- Exact reference preimage for an arbitrary renaming, including collisions. -/
theorem tailCollectR_ref_inv {k : NodeId} :
    tailCollectR G R fresh gp = some (.ref k) ↔
      ∃ i, NSeqRefSpine gp i ∧ fresh i = k := by
  constructor
  · induction gp with
    | nSeq N cont ih =>
        intro h
        obtain ⟨i, hspine, hfresh⟩ := ih h
        exact ⟨i, .nSeq hspine, hfresh⟩
    | choice a b =>
        intro h
        obtain ⟨a', b', _, _, hout⟩ := tailCollectR_choice_some_iff.mp h
        cases hout
    | rcfgPrefix x N cont =>
        intro h
        by_cases hmem : (x, N) ∈ R
        · obtain ⟨tail, _, hout⟩ := (tailCollectR_rcfgPrefix_mem_some_iff hmem).mp h
          cases hout
        · simp [tailCollectR_rcfgPrefix_not_mem cont hmem] at h
    | ref i =>
        intro h
        exact ⟨i, .ref i, GProc.ref.inj (Option.some.inj h)⟩
    | deadlock | recv | send | parallel | leftMerge | commMerge | restrict | project =>
        simp
  · rintro ⟨i, hspine, rfl⟩
    induction hspine with
    | ref i => rfl
    | nSeq _ ih => exact ih

/-- Recover the original endpoint when both identifiers lie in the region
    where the renaming is injective. -/
theorem tailCollectR_ref_iff {L : List NodeId} {j : NodeId}
    (hRefs : ∀ i ∈ tailRefsR R gp, i ∈ L) (hj : j ∈ L)
    (hInj : ∀ ⦃i k⦄, i ∈ L → k ∈ L → fresh i = fresh k → i = k) :
    tailCollectR G R fresh gp = some (.ref (fresh j)) ↔ NSeqRefSpine gp j := by
  constructor
  · intro h
    obtain ⟨i, hspine, heq⟩ := tailCollectR_ref_inv.mp h
    have hi := hRefs i hspine.mem_tailRefsR
    exact hInj hi hj heq ▸ hspine
  · intro h
    exact tailCollectR_ref_inv.mpr ⟨j, h, rfl⟩

end

/-! ## Fresh auxiliary identifiers -/

/-- Greatest original auxiliary index, using zero if there are no auxiliaries. -/
def maxAux (G : ProcessGraph) : Nat :=
  G.nodes.fold max 0 (fun
    | .inl _ => 0
    | .inr k => k)

/-- Allocate above every original auxiliary index, in worklist order.
    Identifiers outside the list all have the same fallback index. -/
def fresh (G : ProcessGraph) (L : List NodeId) (i : NodeId) : NodeId :=
  auxNode (maxAux G + 1 + @List.idxOf NodeId instBEqOfDecidableEq i L)

theorem fresh_inj {L : List NodeId} {i j : NodeId} (hi : i ∈ L) (hj : j ∈ L)
    (heq : fresh G L i = fresh G L j) : i = j :=
  (List.idxOf_inj hi hj).mp (Nat.add_left_cancel (Sum.inr.inj heq))

theorem fresh_inj_iff {L : List NodeId} {i j : NodeId} (hi : i ∈ L) (hj : j ∈ L) :
    fresh G L i = fresh G L j ↔ i = j :=
  ⟨fresh_inj hi hj, congrArg (fresh G L)⟩

theorem fresh_notMem_nodes (G : ProcessGraph) (L : List NodeId) (i : NodeId) :
    fresh G L i ∉ G.nodes := by
  intro h
  have hle : maxAux G + 1 + @List.idxOf NodeId instBEqOfDecidableEq i L ≤ maxAux G := by
    apply (Finset.le_fold_max _).mpr
    exact Or.inr ⟨fresh G L i, h, Nat.le_refl _⟩
  omega

/-- A duplicate-free worklist allocates exactly the consecutive auxiliary
    indices, starting at `maxAux G + 1`, in the order of the returned list. -/
theorem fresh_getElem (G : ProcessGraph) {L : List NodeId} (hL : L.Nodup)
    (n : Nat) (hn : n < L.length) :
    fresh G L L[n] = auxNode (maxAux G + 1 + n) := by
  rw [fresh, List.idxOf_getElem hL n hn]

theorem tailRun_root_refs_mem {L : List NodeId}
    (hrun : tailRun G R (tailRefsR R G.root) ∅ [] = some L) :
    (∀ i ∈ tailRefsR R G.root, i ∈ L) ∧
      ∀ j ∈ L, ∀ i ∈ tailRefsR R (G.label j), i ∈ L := by
  have hreach := (tailRun_root_success G R L hrun).2.1
  refine ⟨?_, ?_⟩
  · intro i hi
    exact (hreach i).mpr ((tailPathTo_iff G R G.root i).mpr ⟨i, hi, .refl i⟩)
  · intro j hj i hi
    exact (hreach i).mpr (tailPathTo_step ((hreach j).mp hj) hi)

theorem tailCollectR_root_ref_iff {L : List NodeId} {j : NodeId}
    (hrun : tailRun G R (tailRefsR R G.root) ∅ [] = some L) (hj : j ∈ L) :
    tailCollectR G R (fresh G L) G.root = some (.ref (fresh G L j)) ↔
      NSeqRefSpine G.root j :=
  tailCollectR_ref_iff (tailRun_root_refs_mem hrun).1 hj
    (fun {_ _} hi hk heq => fresh_inj hi hk heq)

theorem tailCollectR_label_ref_iff {L : List NodeId} {i j : NodeId}
    (hrun : tailRun G R (tailRefsR R G.root) ∅ [] = some L) (hi : i ∈ L) (hj : j ∈ L) :
    tailCollectR G R (fresh G L) (G.label i) = some (.ref (fresh G L j)) ↔
      NSeqRefSpine (G.label i) j :=
  tailCollectR_ref_iff ((tailRun_root_refs_mem hrun).2 i hi) hj
    (fun {_ _} hk hl heq => fresh_inj hk hl heq)

/-! ## Graph assembly -/

/-- Original references retained by the verbatim continuation branches. -/
def tailVerbatimRefs (R : ReconfigSet) : GProc → Finset NodeId
  | .nSeq _ cont => tailVerbatimRefs R cont
  | .choice a b => tailVerbatimRefs R a ∪ tailVerbatimRefs R b
  | .rcfgPrefix x N cont => if (x, N) ∈ R then gprocRefs cont else ∅
  | _ => ∅

theorem tailVerbatimRefs_subset (R : ReconfigSet) (gp : GProc) :
    tailVerbatimRefs R gp ⊆ gprocRefs gp := by
  induction gp with
  | nSeq _ _ ih => exact ih
  | choice a b iha ihb =>
      intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · exact Finset.mem_union_left _ (iha h)
      · exact Finset.mem_union_right _ (ihb h)
  | rcfgPrefix x N cont _ =>
      by_cases h : (x, N) ∈ R <;> simp [tailVerbatimRefs, gprocRefs, h]
  | deadlock | ref | recv | send | parallel | leftMerge | commMerge | restrict | project =>
      simp [tailVerbatimRefs]

/-- Successful local collection exposes exactly the verbatim original
    references and the renamed R-visible references. -/
theorem tailCollectR_refs_iff {rename : NodeId → NodeId} {out : GProc} {i : NodeId}
    (h : tailCollectR G R rename gp = some out) :
    i ∈ gprocRefs out ↔ i ∈ tailVerbatimRefs R gp ∨
      ∃ j ∈ tailRefsR R gp, rename j = i := by
  induction gp generalizing out with
  | deadlock =>
      have hout : out = .deadlock := (Option.some.inj h).symm
      simp [hout, gprocRefs, tailVerbatimRefs, tailRefsR]
  | nSeq _ _ ih => exact ih h
  | choice a b iha ihb =>
      obtain ⟨a', b', ha, hb, rfl⟩ := tailCollectR_choice_some_iff.mp h
      simp only [gprocRefs, tailVerbatimRefs, tailRefsR, Finset.mem_union, List.mem_append,
        iha ha, ihb hb]
      constructor
      · rintro ((ha | ⟨j, hj, heq⟩) | (hb | ⟨j, hj, heq⟩))
        · exact Or.inl (Or.inl ha)
        · exact Or.inr ⟨j, Or.inl hj, heq⟩
        · exact Or.inl (Or.inr hb)
        · exact Or.inr ⟨j, Or.inr hj, heq⟩
      · rintro ((ha | hb) | ⟨j, (hj | hj), heq⟩)
        · exact Or.inl (Or.inl ha)
        · exact Or.inr (Or.inl hb)
        · exact Or.inl (Or.inr ⟨j, hj, heq⟩)
        · exact Or.inr (Or.inr ⟨j, hj, heq⟩)
  | rcfgPrefix x N cont ih =>
      by_cases hmem : (x, N) ∈ R
      · obtain ⟨tail, ht, rfl⟩ := (tailCollectR_rcfgPrefix_mem_some_iff hmem).mp h
        simp only [gprocRefs, Finset.mem_union, tailVerbatimRefs, tailRefsR, if_pos hmem, ih ht]
        constructor
        · rintro (ho | hv | hf)
          · exact Or.inl ho
          · exact Or.inl (tailVerbatimRefs_subset R cont hv)
          · exact Or.inr hf
        · rintro (ho | hf)
          · exact Or.inl ho
          · exact Or.inr (Or.inr hf)
      · rw [tailCollectR_rcfgPrefix_not_mem cont hmem] at h
        have hout : out = .deadlock := (Option.some.inj h).symm
        simp [hout, gprocRefs, tailVerbatimRefs, tailRefsR, hmem]
  | ref j =>
      have hout : out = .ref (rename j) := (Option.some.inj h).symm
      simp [hout, gprocRefs, tailVerbatimRefs, tailRefsR, eq_comm]
  | recv | send | parallel | leftMerge | commMerge | restrict | project => simp at h

theorem tailCollectR_refs_closed {L : List NodeId} {out : GProc}
    (h : tailCollectR G R (fresh G L) gp = some out)
    (hOriginal : gprocRefs gp ⊆ G.nodes) (hFresh : ∀ j ∈ tailRefsR R gp, j ∈ L) :
    gprocRefs out ⊆ G.nodes ∪ L.toFinset.image (fresh G L) := by
  intro i hi
  rcases (tailCollectR_refs_iff h).mp hi with ho | ⟨j, hj, rfl⟩
  · exact Finset.mem_union_left _ (hOriginal (tailVerbatimRefs_subset R gp ho))
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨j, List.mem_toFinset.mpr (hFresh j hj), rfl⟩)

/-- Collect each requested label once and retain its original identifier. -/
def collectTailLabels (collect : NodeId → Option GProc) :
    List NodeId → Option (List (NodeId × GProc))
  | [] => some []
  | i :: rest =>
      (collect i).bind (fun p => (collectTailLabels collect rest).map (List.cons (i, p)))

theorem collectTailLabels_some_iff (collect : NodeId → Option GProc) (L : List NodeId) :
    (∃ entries, collectTailLabels collect L = some entries) ↔
      ∀ i ∈ L, collect i ≠ none := by
  induction L with
  | nil => simp [collectTailLabels]
  | cons i L ih =>
      simp only [List.mem_cons, forall_eq_or_imp, ← ih]
      cases hi : collect i <;>
        simp [collectTailLabels, hi, Option.bind_eq_some, Option.map_eq_some']
      constructor
      · rintro ⟨_, rest, hr, _⟩
        exact ⟨rest, hr⟩
      · rintro ⟨rest, hr⟩
        exact ⟨_, rest, hr, rfl⟩

theorem mem_collectTailLabels {collect : NodeId → Option GProc} {L : List NodeId}
    {entries : List (NodeId × GProc)} (h : collectTailLabels collect L = some entries)
    (i : NodeId) (p : GProc) :
    (i, p) ∈ entries ↔ i ∈ L ∧ collect i = some p := by
  induction L generalizing entries with
  | nil =>
      have he : entries = [] := (Option.some.inj h).symm
      simp [he]
  | cons j L ih =>
      cases hj : collect j with
      | none => simp [collectTailLabels, hj] at h
      | some q =>
          have he : (collectTailLabels collect L).map (List.cons (j, q)) = some entries := by
            simpa only [collectTailLabels, hj, Option.some_bind] using h
          obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some'.mp he
          simp only [List.mem_cons, Prod.mk.injEq, ih hr]
          constructor
          · rintro (⟨rfl, rfl⟩ | ⟨hi, hp⟩)
            · exact ⟨Or.inl rfl, hj⟩
            · exact ⟨Or.inr hi, hp⟩
          · rintro ⟨rfl | hi, hp⟩
            · exact Or.inl ⟨rfl, Option.some.inj (hp.symm.trans hj)⟩
            · exact Or.inr ⟨hi, hp⟩

private def tailGraphLabel (G : ProcessGraph) (L : List NodeId)
    (entries : List (NodeId × GProc)) (k : NodeId) : GProc :=
  if k ∈ G.nodes then G.label k
  else (entries.findSome? (fun (i, p) => if fresh G L i = k then some p else none))
    |>.getD .deadlock

private theorem tailGraphLabel_fresh {L : List NodeId} {entries : List (NodeId × GProc)}
    (h : collectTailLabels (fun j => tailCollectR G R (fresh G L) (G.label j)) L =
      some entries) {i : NodeId} {p : GProc} (hi : i ∈ L)
    (hp : tailCollectR G R (fresh G L) (G.label i) = some p) :
    tailGraphLabel G L entries (fresh G L i) = p := by
  rw [tailGraphLabel, if_neg (fresh_notMem_nodes G L i)]
  let lookup : NodeId × GProc → Option GProc :=
    fun (j, q) => if fresh G L j = fresh G L i then some q else none
  change (entries.findSome? lookup).getD .deadlock = p
  cases hfind : entries.findSome? lookup with
  | none =>
      have hm := (mem_collectTailLabels h i p).mpr ⟨hi, hp⟩
      have := List.findSome?_eq_none_iff.mp hfind (i, p) hm
      simp [lookup] at this
  | some q =>
      obtain ⟨⟨j, t⟩, hm, he⟩ := List.exists_of_findSome?_eq_some hfind
      obtain ⟨hj, ht⟩ := (mem_collectTailLabels h j t).mp hm
      by_cases hf : fresh G L j = fresh G L i
      · have hji := fresh_inj hj hi hf
        subst j
        have htp := Option.some.inj (ht.symm.trans hp)
        simpa [lookup, htp] using he.symm
      · simp [lookup, hf] at he

/-- Assemble the collected root and label table. Original labels take
    precedence, and only the visited identifiers receive fresh nodes. -/
def tailGraphOf (G : ProcessGraph) (R : ReconfigSet) (L : List NodeId)
    (root : GProc) (entries : List (NodeId × GProc))
    (hrun : tailRun G R (tailRefsR R G.root) ∅ [] = some L)
    (hroot : tailCollectR G R (fresh G L) G.root = some root)
    (hentries : collectTailLabels (fun i => tailCollectR G R (fresh G L) (G.label i)) L =
      some entries) : ProcessGraph where
  nodes := G.nodes ∪ L.toFinset.image (fresh G L)
  root := root
  label := tailGraphLabel G L entries
  root_closed := tailCollectR_refs_closed hroot G.root_closed (tailRun_root_refs_mem hrun).1
  closed := by
    intro k hk
    rcases Finset.mem_union.mp hk with ho | hf
    · rw [tailGraphLabel, if_pos ho]
      exact fun _ hi => Finset.mem_union_left _ (G.closed k ho hi)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
      have hiL := List.mem_toFinset.mp hi
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp
        ((collectTailLabels_some_iff _ L).mp ⟨entries, hentries⟩ i hiL)
      rw [tailGraphLabel_fresh hentries hiL hp]
      exact tailCollectR_refs_closed hp
        (G.closed i ((tailRun_root_success G R L hrun).2.2 i hiL))
        ((tailRun_root_refs_mem hrun).2 i hiL)

/-- Traverse the R-visible region, collect its root and labels, and assemble. -/
def graphTail (G : ProcessGraph) (R : ReconfigSet) : Option ProcessGraph :=
  match hrun : tailRun G R (tailRefsR R G.root) ∅ [] with
  | none => none
  | some L =>
      match hroot : tailCollectR G R (fresh G L) G.root with
      | none => none
      | some root =>
          match hentries : collectTailLabels
            (fun i => tailCollectR G R (fresh G L) (G.label i)) L with
          | none => none
          | some entries => some (tailGraphOf G R L root entries hrun hroot hentries)

/-- Exact collection domain, with the fresh allocator determined by the
    actual root traversal. -/
def GraphTailDomain (G : ProcessGraph) (R : ReconfigSet) : Prop :=
  ∃ L, tailRun G R (tailRefsR R G.root) ∅ [] = some L ∧
    tailCollectR G R (fresh G L) G.root ≠ none ∧
    ∀ i, TailPathTo G R G.root i → tailCollectR G R (fresh G L) (G.label i) ≠ none

theorem graphTail_eq_some_tailGraphOf {L : List NodeId} {root : GProc}
    {entries : List (NodeId × GProc)}
    (hrun : tailRun G R (tailRefsR R G.root) ∅ [] = some L)
    (hroot : tailCollectR G R (fresh G L) G.root = some root)
    (hentries : collectTailLabels (fun i => tailCollectR G R (fresh G L) (G.label i)) L =
      some entries) :
    graphTail G R = some (tailGraphOf G R L root entries hrun hroot hentries) := by
  unfold graphTail
  split
  · simp_all
  · rename_i found hf
    have he := Option.some.inj (hf.symm.trans hrun)
    subst found
    split
    · simp_all
    · rename_i found hf
      have he := Option.some.inj (hf.symm.trans hroot)
      subst found
      split
      · simp_all
      · rename_i found hf
        have he := Option.some.inj (hf.symm.trans hentries)
        subst found
        rfl

theorem graphTail_domain_some (h : GraphTailDomain G R) :
    ∃ G', graphTail G R = some G' := by
  obtain ⟨L, hrun, hr, hl⟩ := h
  obtain ⟨root, hroot⟩ := Option.ne_none_iff_exists'.mp hr
  obtain ⟨entries, hentries⟩ := (collectTailLabels_some_iff _ L).mpr
    (fun i hi => hl i ((tailRun_root_success G R L hrun).2.1 i |>.mp hi))
  exact ⟨_, graphTail_eq_some_tailGraphOf hrun hroot hentries⟩

theorem graphTail_some_inv {G' : ProcessGraph} (h : graphTail G R = some G') :
    ∃ (L : List NodeId) (root : GProc) (entries : List (NodeId × GProc))
      (hrun : tailRun G R (tailRefsR R G.root) ∅ [] = some L)
      (hroot : tailCollectR G R (fresh G L) G.root = some root)
      (hentries : collectTailLabels (fun i => tailCollectR G R (fresh G L) (G.label i)) L =
        some entries), G' = tailGraphOf G R L root entries hrun hroot hentries := by
  unfold graphTail at h
  split at h
  · contradiction
  · rename_i L hrun
    split at h
    · contradiction
    · rename_i root hroot
      split at h
      · contradiction
      · rename_i entries hentries
        exact ⟨L, root, entries, hrun, hroot, hentries, (Option.some.inj h).symm⟩

theorem graphTail_domain_iff : GraphTailDomain G R ↔ ∃ G', graphTail G R = some G' := by
  refine ⟨graphTail_domain_some, ?_⟩
  rintro ⟨G', h⟩
  obtain ⟨L, root, entries, hrun, hroot, hentries, _⟩ := graphTail_some_inv h
  refine ⟨L, hrun, Option.ne_none_iff_exists'.mpr ⟨root, hroot⟩, ?_⟩
  intro i hi
  exact (collectTailLabels_some_iff _ L).mp ⟨entries, hentries⟩ i
    ((tailRun_root_success G R L hrun).2.1 i |>.mpr hi)

section

variable {L : List NodeId} {root : GProc} {entries : List (NodeId × GProc)}
  {hrun : tailRun G R (tailRefsR R G.root) ∅ [] = some L}
  {hroot : tailCollectR G R (fresh G L) G.root = some root}
  {hentries : collectTailLabels (fun i => tailCollectR G R (fresh G L) (G.label i)) L =
    some entries}

theorem tailGraphOf_nodes :
    (tailGraphOf G R L root entries hrun hroot hentries).nodes =
      G.nodes ∪ L.toFinset.image (fresh G L) := rfl

theorem tailGraphOf_root :
    (tailGraphOf G R L root entries hrun hroot hentries).root = root := rfl

theorem tailGraphOf_label_original {i : NodeId} (hi : i ∈ G.nodes) :
    (tailGraphOf G R L root entries hrun hroot hentries).label i = G.label i :=
  if_pos hi

theorem tailGraphOf_label_fresh {i : NodeId} {p : GProc} (hi : i ∈ L)
    (hp : tailCollectR G R (fresh G L) (G.label i) = some p) :
    (tailGraphOf G R L root entries hrun hroot hentries).label (fresh G L i) = p :=
  tailGraphLabel_fresh hentries hi hp

theorem tailGraphOf_label_outside {i : NodeId}
    (hi : i ∉ (tailGraphOf G R L root entries hrun hroot hentries).nodes) :
    (tailGraphOf G R L root entries hrun hroot hentries).label i = .deadlock := by
  have ho : i ∉ G.nodes := fun hm => hi (Finset.mem_union_left _ hm)
  change tailGraphLabel G L entries i = .deadlock
  rw [tailGraphLabel, if_neg ho]
  have hfind : entries.findSome? (fun (j, p) => if fresh G L j = i then some p else none)
      = none := by
    apply List.findSome?_eq_none_iff.mpr
    rintro ⟨j, p⟩ hm
    have hj := ((mem_collectTailLabels hentries j p).mp hm).1
    have hne : fresh G L j ≠ i := fun he =>
      hi (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, List.mem_toFinset.mpr hj, he⟩))
    simp [hne]
  rw [hfind]
  rfl

end

/-! ## R-independent supportedness -/

/-- Supported local syntax, checking the continuation of every
    reconfiguration and treating a live reference as a leaf. -/
inductive TailShapeOk (G : ProcessGraph) : GProc → Prop
  | deadlock : TailShapeOk G .deadlock
  | nSeq {N cont} : TailShapeOk G cont → TailShapeOk G (.nSeq N cont)
  | choice {a b} : TailShapeOk G a → TailShapeOk G b → TailShapeOk G (.choice a b)
  | rcfgPrefix {x N cont} : TailShapeOk G cont → TailShapeOk G (.rcfgPrefix x N cont)
  | ref {i} : i ∈ G.nodes → TailShapeOk G (.ref i)

/-- The root and all labels reachable along syntactic references have
    supported local syntax. Reachability includes references behind any
    reconfiguration. -/
def GraphTailSupported (G : ProcessGraph) : Prop :=
  TailShapeOk G G.root ∧
    ∀ i ∈ gprocRefs G.root, ∀ j,
      Relation.ReflTransGen (fun a b => b ∈ gprocRefs (G.label a)) i j →
        TailShapeOk G (G.label j)

theorem TailShapeOk.collect_ne_none {rename : NodeId → NodeId} (h : TailShapeOk G gp) :
    tailCollectR G R rename gp ≠ none := by
  induction h with
  | deadlock => simp
  | nSeq _ ih => exact ih
  | choice _ _ iha ihb => simp [tailCollectR_choice_none_iff, iha, ihb]
  | @rcfgPrefix x N cont _ ih =>
      by_cases hm : (x, N) ∈ R
      · rwa [ne_eq, tailCollectR_rcfgPrefix_mem_none_iff hm]
      · simp [tailCollectR_rcfgPrefix_not_mem cont hm]
  | ref _ => simp

theorem graphTailSupported_implies_domain (h : GraphTailSupported G) : GraphTailDomain G R := by
  obtain ⟨L, hrun⟩ := tailRun_root_some G R
  refine ⟨L, hrun, h.1.collect_ne_none, ?_⟩
  intro j hj
  obtain ⟨i, hi, hreach⟩ := (tailPathTo_iff G R G.root j).mp hj
  apply TailShapeOk.collect_ne_none
  refine h.2 i (tailRefsR_subset_gprocRefs R G.root hi) j ?_
  clear hj hi
  induction hreach with
  | refl => exact .refl
  | step hv _ ih => exact ih.head (tailRefsR_subset_gprocRefs R _ hv)

theorem graphTail_supported_some (h : GraphTailSupported G) :
    ∃ G', graphTail G R = some G' :=
  graphTail_domain_some (graphTailSupported_implies_domain h)

/-! ## Head extraction after successful graph-tail extraction -/

private def HeadCollectOk (live : NodeId → Prop) (p : GProc) : Prop :=
  headCollect p ≠ none ∧ ∀ i ∈ headRefs p, live i

private theorem HeadCollectOk.deadlock (live : NodeId → Prop) :
    HeadCollectOk live .deadlock := by
  simp [HeadCollectOk, headCollect_deadlock, headRefs]

private theorem HeadCollectOk.nSeq {live : NodeId → Prop} {p : GProc}
    (h : HeadCollectOk live p) (N : NetKAT) : HeadCollectOk live (.nSeq N p) := by
  exact ⟨by simpa [headCollect_nSeq] using h.1, h.2⟩

private theorem HeadCollectOk.choice {live : NodeId → Prop} {a b : GProc}
    (ha : HeadCollectOk live a) (hb : HeadCollectOk live b) :
    HeadCollectOk live (.choice a b) := by
  obtain ⟨A, hA⟩ := Option.ne_none_iff_exists'.mp ha.1
  obtain ⟨B, hB⟩ := Option.ne_none_iff_exists'.mp hb.1
  refine ⟨by simp [headCollect_choice, hA, hB], ?_⟩
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact ha.2 i hi
  · exact hb.2 i hi

private theorem HeadCollectOk.ref {live : NodeId → Prop} {i : NodeId} (h : live i) :
    HeadCollectOk live (.ref i) := by
  simp [HeadCollectOk, headCollect_ref, headRefs, h]

/-- Successful collection guarantees that the input and output both
    collect locally for head. Their head references stay within any
    region containing the exposed original and renamed identifiers. -/
private theorem tailCollectR_head_collect_ok {rename : NodeId → NodeId} {out : GProc}
    {live : NodeId → Prop} (h : tailCollectR G R rename gp = some out)
    (hLive : ∀ i ∈ tailRefsR R gp, live i ∧ live (rename i)) :
    HeadCollectOk live gp ∧ HeadCollectOk live out := by
  induction gp generalizing out with
  | deadlock =>
      have hout : out = .deadlock := (Option.some.inj h).symm
      subst out
      exact ⟨.deadlock live, .deadlock live⟩
  | nSeq N cont ih =>
      obtain ⟨hc, ho⟩ := ih h hLive
      exact ⟨hc.nSeq N, ho⟩
  | choice a b iha ihb =>
      obtain ⟨a', b', ha, hb, rfl⟩ := tailCollectR_choice_some_iff.mp h
      obtain ⟨hA, hA'⟩ := iha ha (fun i hi => hLive i (List.mem_append_left _ hi))
      obtain ⟨hB, hB'⟩ := ihb hb (fun i hi => hLive i (List.mem_append_right _ hi))
      exact ⟨hA.choice hB, hA'.choice hB'⟩
  | rcfgPrefix x N cont ih =>
      have hPrefix : HeadCollectOk live (.rcfgPrefix x N cont) := by
        simp [HeadCollectOk, headCollect_rcfgPrefix, headRefs]
      by_cases hm : (x, N) ∈ R
      · obtain ⟨p, hp, rfl⟩ := (tailCollectR_rcfgPrefix_mem_some_iff hm).mp h
        obtain ⟨hc, hp⟩ := ih hp (fun i hi => hLive i (by simpa [tailRefsR, hm] using hi))
        exact ⟨hPrefix, hc.choice hp⟩
      · rw [tailCollectR_rcfgPrefix_not_mem cont hm] at h
        have hout : out = .deadlock := (Option.some.inj h).symm
        subst out
        exact ⟨hPrefix, .deadlock live⟩
  | ref i =>
      have hout : out = .ref (rename i) := (Option.some.inj h).symm
      subst out
      obtain ⟨hi, hRename⟩ := hLive i (by simp [tailRefsR])
      exact ⟨.ref hi, .ref hRename⟩
  | recv | send | parallel | leftMerge | commMerge | restrict | project => simp at h

/-- Head extraction succeeds on every successfully assembled tail graph. -/
theorem graphTail_head_some {G' : ProcessGraph} (h : graphTail G R = some G') :
    ∃ H, graphHead G' = some H := by
  obtain ⟨L, root, entries, hrun, hroot, hentries, rfl⟩ := graphTail_some_inv h
  let out := tailGraphOf G R L root entries hrun hroot hentries
  let live : NodeId → Prop := fun k => k ∈ L ∨ ∃ j ∈ L, fresh G L j = k
  have hLocal {p q : GProc} (hcol : tailCollectR G R (fresh G L) p = some q)
      (hRefs : ∀ i ∈ tailRefsR R p, i ∈ L) : HeadCollectOk live p ∧ HeadCollectOk live q :=
    tailCollectR_head_collect_ok hcol (fun i hi =>
      ⟨Or.inl (hRefs i hi), Or.inr ⟨i, hRefs i hi, rfl⟩⟩)
  have hRoot : HeadCollectOk live out.root := (hLocal hroot (tailRun_root_refs_mem hrun).1).2
  have hLabel : ∀ i, live i → HeadCollectOk live (out.label i) := by
    have hCollect (i : NodeId) (hi : i ∈ L) :=
      Option.ne_none_iff_exists'.mp ((collectTailLabels_some_iff _ L).mp ⟨entries, hentries⟩ i hi)
    intro i hi
    rcases hi with hi | ⟨j, hj, rfl⟩
    · rw [show out.label i = G.label i from
        tailGraphOf_label_original ((tailRun_root_success G R L hrun).2.2 i hi)]
      obtain ⟨p, hp⟩ := hCollect i hi
      exact (hLocal hp ((tailRun_root_refs_mem hrun).2 i hi)).1
    · obtain ⟨p, hp⟩ := hCollect j hj
      rw [show out.label (fresh G L j) = p from tailGraphOf_label_fresh hj hp]
      rcases tailCollectR_image_shape hp with rfl | ⟨a, b, rfl⟩ | ⟨i, rfl⟩
      · exact .deadlock live
      · exact (hLocal hp ((tailRun_root_refs_mem hrun).2 j hj)).2
      · obtain ⟨k, hk, heq⟩ := tailCollectR_ref_inv.mp hp
        exact .ref (Or.inr ⟨k, (tailRun_root_refs_mem hrun).2 j hj k hk.mem_tailRefsR, heq⟩)
  have hReach (i : NodeId) (hi : HeadPathTo out out.root i) : live i := by
    rcases headPathTo_refs_decomp out out.root i hi with hiDirect | ⟨j, hj, hreach⟩
    · exact hRoot.2 i hiDirect
    · have hjLive := hRoot.2 j hj
      clear hi hj
      induction hreach with
      | refl => exact hjLive
      | step _ v _ hv _ ih => exact ih ((hLabel _ hjLive).2 v hv)
  change ∃ H, graphHead out = some H
  cases hrunHead : headRun out (headRefsList out.root) ∅ [] with
  | none =>
      obtain ⟨j, hj, hMissing⟩ := headRun_root_failure out hrunHead
      exact absurd (headPathTo_nodes_closed out j hj) hMissing
  | some visits =>
      obtain ⟨H₀, hH₀⟩ := Option.ne_none_iff_exists'.mp hRoot.1
      obtain ⟨H, hH⟩ := unionOverList_some (fun i => headCollect (out.label i))
        visits (headCollect out.root) H₀ hH₀ (fun i hi =>
          Option.ne_none_iff_exists'.mp
            (hLabel i (hReach i ((headRun_root_success out visits hrunHead).2 i hi).1)).1)
      exact ⟨H, by simpa [graphHead, hrunHead, graphHeadUnion] using hH⟩

/-! ## Semantic correctness of the assembled tail -/

/-- Head derivations of a closed original term are invariant under extending
    the graph while preserving its original labels. -/
theorem graphHeadSpec_agree {G' : ProcessGraph}
    (hAgree : ∀ i ∈ G.nodes, G'.label i = G.label i)
    (hClosed : gprocRefs gp ⊆ G.nodes) :
    GraphHeadSpec G' gp σ τ ↔ GraphHeadSpec G gp σ τ := by
  have transfer {src dst : ProcessGraph}
      (hSrc : ∀ i ∈ G.nodes, src.label i = G.label i)
      (hDst : ∀ i ∈ G.nodes, dst.label i = G.label i)
      {p σ τ} (h : GraphHeadSpec src p σ τ) :
      gprocRefs p ⊆ G.nodes → GraphHeadSpec dst p σ τ := by
    induction h with
    | nSeq_of_sem _ _ _ _ h => exact fun _ => .nSeq_of_sem _ _ _ _ h
    | nSeq_of_tail _ _ _ _ _ ih => exact fun hc => .nSeq_of_tail _ _ _ _ (ih hc)
    | choice_left _ _ _ _ _ ih =>
        exact fun hc => .choice_left _ _ _ _ (ih (Finset.union_subset_iff.mp hc).1)
    | choice_right _ _ _ _ _ ih =>
        exact fun hc => .choice_right _ _ _ _ (ih (Finset.union_subset_iff.mp hc).2)
    | ref_of i σ τ _ ih =>
        intro hc
        have hi : i ∈ G.nodes := hc (Finset.mem_singleton_self i)
        apply GraphHeadSpec.ref_of
        rw [hDst i hi, ← hSrc i hi]
        exact ih (by rw [hSrc i hi]; exact G.closed i hi)
  exact ⟨fun h => transfer hAgree (fun _ _ => rfl) h hClosed,
    fun h => transfer (fun _ _ => rfl) hAgree h hClosed⟩

private def TailRegion (G : ProcessGraph) (R : ReconfigSet) (L : List NodeId) (p : GProc) :
    Prop :=
  gprocRefs p ⊆ G.nodes ∧ ∀ i ∈ tailRefsR R p, i ∈ L

private theorem tailRegion_choice {L : List NodeId} {a b : GProc} :
    TailRegion G R L (.choice a b) ↔ TailRegion G R L a ∧ TailRegion G R L b := by
  simp only [TailRegion, gprocRefs, Finset.union_subset_iff, tailRefsR, List.mem_append,
    or_imp, forall_and]
  exact and_and_and_comm

private theorem tailRegion_rcfg {L : List NodeId} {x : Channel} {N : NetKAT}
    {p : GProc} (h : (x, N) ∈ R) :
    TailRegion G R L (.rcfgPrefix x N p) ↔ TailRegion G R L p := by
  simp only [TailRegion, gprocRefs, tailRefsR, if_pos h]

private theorem NSeqRefSpine.liftTail {i : NodeId} (h : NSeqRefSpine gp i)
    (ht : GraphTailSpec G R (G.label i) σ τ) : GraphTailSpec G R gp σ τ := by
  induction h with
  | ref i => exact .ref_of i _ _ ht
  | nSeq _ ih => exact .nSeq_of _ _ _ _ (ih ht)

section

variable {G' : ProcessGraph} {L : List NodeId}

private theorem tailCollectR_choice_sound (hAgree : ∀ i ∈ G.nodes, G'.label i = G.label i)
    {a b : GProc}
    (hBranch :
      (GraphHeadSpec G' a σ τ ∧
        (∀ p, tailCollectR G R (fresh G L) p = some a →
          TailRegion G R L p → GraphTailSpec G R p σ τ)) ∨
      (∀ p, tailCollectR G R (fresh G L) p = some b →
        TailRegion G R L p → GraphTailSpec G R p σ τ))
    (hc : tailCollectR G R (fresh G L) gp = some (.choice a b))
    (hr : TailRegion G R L gp) : GraphTailSpec G R gp σ τ := by
  induction gp with
  | nSeq N p ih => exact .nSeq_of N p _ _ (ih hc hr)
  | choice p q =>
      obtain ⟨a', b', ha, hb, he⟩ := tailCollectR_choice_some_iff.mp hc
      cases he
      obtain ⟨hp, hq⟩ := tailRegion_choice.mp hr
      rcases hBranch with ⟨_, ih⟩ | ih
      · exact .choice_left p q _ _ (ih p ha hp)
      · exact .choice_right p q _ _ (ih q hb hq)
  | rcfgPrefix x N p =>
      by_cases hm : (x, N) ∈ R
      · obtain ⟨b', hb, he⟩ := (tailCollectR_rcfgPrefix_mem_some_iff hm).mp hc
        cases he
        have hp := (tailRegion_rcfg hm).mp hr
        apply GraphTailSpec.rcfgPrefix_of _ _ _ _ _ hm
        rcases hBranch with ⟨hHead, _⟩ | ih
        · exact head_in_allR ((graphHeadSpec_agree hAgree hp.1).mp hHead)
        · exact tail_in_allR (ih _ hb hp)
      · simp [tailCollectR_rcfgPrefix_not_mem p hm] at hc
  | deadlock | ref | recv | send | parallel | leftMerge | commMerge | restrict | project =>
      simp at hc

/-- Each head derivation in the collected term either uses a verbatim
    continuation or follows the collected syntax and fresh labels. -/
private theorem tailCollectR_sound (hAgree : ∀ i ∈ G.nodes, G'.label i = G.label i)
    (hLabels : ∀ i ∈ L, TailRegion G R L (G.label i) ∧
      tailCollectR G R (fresh G L) (G.label i) = some (G'.label (fresh G L i)))
    {out : GProc} (hh : GraphHeadSpec G' out σ τ) :
    ∀ p, tailCollectR G R (fresh G L) p = some out →
      TailRegion G R L p → GraphTailSpec G R p σ τ := by
  induction hh with
  | nSeq_of_sem | nSeq_of_tail =>
      intro p hc _
      rcases tailCollectR_image_shape hc with he | ⟨a, b, he⟩ | ⟨i, he⟩ <;> cases he
  | choice_left a b σ τ hh ih =>
      exact fun _ => tailCollectR_choice_sound hAgree (Or.inl ⟨hh, ih⟩)
  | choice_right a b σ τ hh ih =>
      exact fun _ => tailCollectR_choice_sound hAgree (Or.inr ih)
  | ref_of k σ τ hh ih =>
      intro p hc hr
      obtain ⟨i, hSpine, rfl⟩ := tailCollectR_ref_inv.mp hc
      obtain ⟨hRegion, hCol⟩ := hLabels i (hr.2 i hSpine.mem_tailRefsR)
      exact hSpine.liftTail (ih _ hCol hRegion)

private theorem tailCollectR_allR_complete
    (hAgree : ∀ i ∈ G.nodes, G'.label i = G.label i)
    (hLabels : ∀ i ∈ L, TailRegion G R L (G.label i) ∧
      tailCollectR G R (fresh G L) (G.label i) = some (G'.label (fresh G L i)))
    (hh : GraphAllRSpec G R gp σ τ) :
    ∀ {out}, tailCollectR G R (fresh G L) gp = some out →
      TailRegion G R L gp → GraphHeadSpec G gp σ τ ∨ GraphHeadSpec G' out σ τ := by
  induction hh with
  | nSeq_of_sem N p σ τ h => exact fun _ _ => Or.inl (.nSeq_of_sem N p σ τ h)
  | nSeq_of N p σ τ _ ih =>
      intro out hc hr
      exact (ih hc hr).imp (.nSeq_of_tail N p σ τ) id
  | choice_left a b σ τ _ ih =>
      intro out hc hr
      obtain ⟨a', b', ha, _, rfl⟩ := tailCollectR_choice_some_iff.mp hc
      exact (ih ha (tailRegion_choice.mp hr).1).imp
        (.choice_left a b σ τ) (.choice_left a' b' σ τ)
  | choice_right a b σ τ _ ih =>
      intro out hc hr
      obtain ⟨a', b', _, hb, rfl⟩ := tailCollectR_choice_some_iff.mp hc
      exact (ih hb (tailRegion_choice.mp hr).2).imp
        (.choice_right a b σ τ) (.choice_right a' b' σ τ)
  | rcfgPrefix_of x N p σ τ hm _ ih =>
      intro out hc hr
      obtain ⟨p', hp, rfl⟩ := (tailCollectR_rcfgPrefix_mem_some_iff hm).mp hc
      have hRegion := (tailRegion_rcfg hm).mp hr
      apply Or.inr
      rcases ih hp hRegion with hHead | hTail
      · exact .choice_left p p' σ τ ((graphHeadSpec_agree hAgree hRegion.1).mpr hHead)
      · exact .choice_right p p' σ τ hTail
  | ref_of i σ τ _ ih =>
      intro out hc hr
      have he := Option.some.inj hc
      subst out
      obtain ⟨hRegion, hCol⟩ := hLabels i (hr.2 i (by simp [tailRefsR]))
      exact (ih hCol hRegion).imp (.ref_of i σ τ) (.ref_of (fresh G L i) σ τ)

private theorem tailCollectR_complete
    (hAgree : ∀ i ∈ G.nodes, G'.label i = G.label i)
    (hLabels : ∀ i ∈ L, TailRegion G R L (G.label i) ∧
      tailCollectR G R (fresh G L) (G.label i) = some (G'.label (fresh G L i)))
    (hh : GraphTailSpec G R gp σ τ) :
    ∀ {out}, tailCollectR G R (fresh G L) gp = some out →
      TailRegion G R L gp → GraphHeadSpec G' out σ τ := by
  induction hh with
  | nSeq_of _ _ _ _ _ ih => exact fun hc hr => ih hc hr
  | choice_left a b σ τ _ ih =>
      intro out hc hr
      obtain ⟨a', b', ha, _, rfl⟩ := tailCollectR_choice_some_iff.mp hc
      exact .choice_left a' b' σ τ (ih ha (tailRegion_choice.mp hr).1)
  | choice_right a b σ τ _ ih =>
      intro out hc hr
      obtain ⟨a', b', _, hb, rfl⟩ := tailCollectR_choice_some_iff.mp hc
      exact .choice_right a' b' σ τ (ih hb (tailRegion_choice.mp hr).2)
  | rcfgPrefix_of x N p σ τ hm hAll =>
      intro out hc hr
      obtain ⟨p', hp, rfl⟩ := (tailCollectR_rcfgPrefix_mem_some_iff hm).mp hc
      have hRegion := (tailRegion_rcfg hm).mp hr
      rcases tailCollectR_allR_complete hAgree hLabels hAll hp hRegion with hHead | hTail
      · exact .choice_left p p' σ τ ((graphHeadSpec_agree hAgree hRegion.1).mpr hHead)
      · exact .choice_right p p' σ τ hTail
  | ref_of i σ τ _ ih =>
      intro out hc hr
      have he := Option.some.inj hc
      subst out
      obtain ⟨hRegion, hCol⟩ := hLabels i (hr.2 i (by simp [tailRefsR]))
      exact .ref_of (fresh G L i) σ τ (ih hCol hRegion)

end

theorem graphTail_bridge {G' : ProcessGraph} (h : graphTail G R = some G') :
    GraphHeadSpec G' G'.root σ τ ↔ GraphTailSpec G R G.root σ τ := by
  obtain ⟨L, root, entries, hRun, hRoot, hEntries, rfl⟩ := graphTail_some_inv h
  let out := tailGraphOf G R L root entries hRun hRoot hEntries
  have hAgree : ∀ i ∈ G.nodes, out.label i = G.label i :=
    fun _ hi => tailGraphOf_label_original hi
  have hLabels : ∀ i ∈ L, TailRegion G R L (G.label i) ∧
      tailCollectR G R (fresh G L) (G.label i) = some (out.label (fresh G L i)) := by
    intro i hi
    have hNode := (tailRun_root_success G R L hRun).2.2 i hi
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp
      ((collectTailLabels_some_iff _ L).mp ⟨entries, hEntries⟩ i hi)
    rw [show out.label (fresh G L i) = p from tailGraphOf_label_fresh hi hp]
    exact ⟨⟨G.closed i hNode, (tailRun_root_refs_mem hRun).2 i hi⟩, hp⟩
  have hRegion : TailRegion G R L G.root :=
    ⟨G.root_closed, (tailRun_root_refs_mem hRun).1⟩
  change GraphHeadSpec out root σ τ ↔ GraphTailSpec G R G.root σ τ
  exact ⟨fun hh => tailCollectR_sound hAgree hLabels hh _ hRoot hRegion,
    fun ht => tailCollectR_complete hAgree hLabels ht hRoot hRegion⟩

theorem graphTail_sound {G' : ProcessGraph} {H : NetKAT}
    (h : graphTail G R = some G') (hHead : graphHead G' = some H)
    (hSem : Semantics H σ τ) : GraphTailSpec G R G.root σ τ :=
  (graphTail_bridge h).mp (graphHead_sound G' H hHead σ τ hSem)

theorem graphTail_complete {G' : ProcessGraph} {H : NetKAT}
    (h : graphTail G R = some G') (hHead : graphHead G' = some H)
    (hSpec : GraphTailSpec G R G.root σ τ) : Semantics H σ τ :=
  graphHead_complete G' H hHead σ τ ((graphTail_bridge h).mpr hSpec)

theorem graphTail_spec_iff_of_domain (h : GraphTailDomain G R) :
    GraphTailSpec G R G.root σ τ ↔
      ∃ G' H, graphTail G R = some G' ∧ graphHead G' = some H ∧ Semantics H σ τ := by
  constructor
  · intro hSpec
    obtain ⟨G', hTail⟩ := graphTail_domain_some h
    obtain ⟨H, hHead⟩ := graphTail_head_some hTail
    exact ⟨G', H, hTail, hHead, graphTail_complete hTail hHead hSpec⟩
  · rintro ⟨G', H, hTail, hHead, hSem⟩
    exact graphTail_sound hTail hHead hSem

theorem graphTail_spec_iff (h : GraphTailSupported G) :
    GraphTailSpec G R G.root σ τ ↔
      ∃ G' H, graphTail G R = some G' ∧ graphHead G' = some H ∧ Semantics H σ τ :=
  graphTail_spec_iff_of_domain (graphTailSupported_implies_domain h)

/-- Supported local syntax of the root and all labels suffices for both
    extractors on a closed graph. -/
theorem graphSupported_of_shapes {Q : ProcessGraph}
    (rootShape : TailShapeOk Q Q.root)
    (labelShape : ∀ i ∈ Q.nodes, TailShapeOk Q (Q.label i)) :
    GraphHeadSupported Q ∧ GraphTailSupported Q := by
  refine ⟨⟨?_, fun i => headPathTo_nodes_closed Q i⟩, ⟨rootShape, ?_⟩⟩
  · have shape {p q} (hSub : HeadSub Q p q) : TailShapeOk Q p → HeadShapeOk Q q := by
      induction hSub with
      | refl p =>
          intro hp
          cases hp
          · exact .deadlock
          · exact .nSeq _ _
          · exact .choice _ _
          · exact .rcfgPrefix _ _ _
          · exact .ref _ (by assumption)
      | nSeq _ _ _ _ ih => intro hp; cases hp; exact ih (by assumption)
      | choice_left _ _ _ _ ih => intro hp; cases hp; exact ih (by assumption)
      | choice_right _ _ _ _ ih => intro hp; cases hp; exact ih (by assumption)
      | ref i _ _ ih => intro hp; cases hp; exact ih (labelShape i (by assumption))
    exact fun _ hSub => shape hSub rootShape
  · intro i hi j hReach
    apply labelShape
    induction hReach with
    | refl => exact Q.root_closed hi
    | tail _ hEdge ih => exact Q.closed _ ih hEdge


/-- The original continuations selected by a structural tail. -/
inductive TailSelect (G : ProcessGraph) (R : ReconfigSet) : GProc → GProc → Prop
  | packet : TailSelect G R p q → TailSelect G R (.nSeq N p) q
  | left : TailSelect G R p q → TailSelect G R (.choice p r) q
  | right : TailSelect G R r q → TailSelect G R (.choice p r) q
  | ref : TailSelect G R (G.label i) q → TailSelect G R (.ref i) q
  | stop : (x, N) ∈ R → TailSelect G R (.rcfgPrefix x N p) p
  | next : (x, N) ∈ R → TailSelect G R p q → TailSelect G R (.rcfgPrefix x N p) q

section
variable {G Q : ProcessGraph} {R : ReconfigSet} {L : List NodeId}
variable {pt hl pt' hl' : List CtxPkt} {a : Action} {dst : GProc}

private theorem select_closed {p q : GProc} (s : TailSelect G R p q) :
    gprocRefs p ⊆ G.nodes → gprocRefs q ⊆ G.nodes := by
  induction s with
  | packet _ ih | next _ _ ih => exact ih
  | left _ ih => exact fun hc => ih (Finset.union_subset_iff.mp hc).1
  | right _ ih => exact fun hc => ih (Finset.union_subset_iff.mp hc).2
  | ref _ ih => exact fun hc => ih (G.closed _ (hc (Finset.mem_singleton_self _)))
  | stop => exact id

private theorem select_spine {p q : GProc} {i : NodeId} (h : NSeqRefSpine p i)
    (s : TailSelect G R (G.label i) q) : TailSelect G R p q := by
  induction h with
  | ref => exact .ref s
  | nSeq _ ih => exact .packet (ih s)

private theorem collectedChoice_select {p l r : GProc}
    (found :
      ((gprocRefs l ⊆ G.nodes → GStep G ⟨l, pt, hl⟩ a ⟨dst, pt', hl'⟩) ∧
        (∀ p, tailCollectR G R (fresh G L) p = some l → TailRegion G R L p →
          ∃ q, TailSelect G R p q ∧ GStep G ⟨q, pt, hl⟩ a ⟨dst, pt', hl'⟩)) ∨
      (∀ p, tailCollectR G R (fresh G L) p = some r → TailRegion G R L p →
          ∃ q, TailSelect G R p q ∧ GStep G ⟨q, pt, hl⟩ a ⟨dst, pt', hl'⟩))
    (coll : tailCollectR G R (fresh G L) p = some (.choice l r))
    (region : TailRegion G R L p) :
    ∃ q, TailSelect G R p q ∧ GStep G ⟨q, pt, hl⟩ a ⟨dst, pt', hl'⟩ := by
  induction p with
  | nSeq N p ih =>
      obtain ⟨q, sel, step⟩ := ih coll region
      exact ⟨q, .packet sel, step⟩
  | choice p q =>
      obtain ⟨l', r', hL, hR, eq⟩ := tailCollectR_choice_some_iff.mp coll
      cases eq
      obtain ⟨hP, hQ⟩ := tailRegion_choice.mp region
      rcases found with ⟨_, useLeft⟩ | useRight
      · obtain ⟨z, sel, step⟩ := useLeft p hL hP
        exact ⟨z, .left sel, step⟩
      · obtain ⟨z, sel, step⟩ := useRight q hR hQ
        exact ⟨z, .right sel, step⟩
  | rcfgPrefix x N p =>
      by_cases hm : (x, N) ∈ R
      · obtain ⟨r', hR, eq⟩ := (tailCollectR_rcfgPrefix_mem_some_iff hm).mp coll
        cases eq
        have hP := (tailRegion_rcfg hm).mp region
        rcases found with ⟨verbatim, _⟩ | useRight
        · exact ⟨_, .stop hm, verbatim hP.1⟩
        · obtain ⟨q, sel, step⟩ := useRight _ hR hP
          exact ⟨q, .next hm sel, step⟩
      · simp [tailCollectR_rcfgPrefix_not_mem _ hm] at coll
  | deadlock | ref | recv | send | parallel | leftMerge | commMerge | restrict | project =>
      simp at coll

private theorem collectedStep_sound
    (agree : ∀ i ∈ G.nodes, Q.label i = G.label i)
    (labels : ∀ i ∈ L, TailRegion G R L (G.label i) ∧
      tailCollectR G R (fresh G L) (G.label i) = some (Q.label (fresh G L i)))
    {src out : GConfig} {a : Action} (step : GStep Q src a out) :
    ∀ p, tailCollectR G R (fresh G L) p = some src.proc → TailRegion G R L p →
      ∃ q, TailSelect G R p q ∧ GStep G {src with proc := q} a out := by
  have closed : ∀ i ∈ G.nodes, gprocRefs (Q.label i) ⊆ G.nodes := by
    intro i hi; rw [agree i hi]; exact G.closed i hi
  induction step with
  | choice_l l r _ _ _ _ _ _ inner ih =>
      exact fun _ => collectedChoice_select
        (Or.inl ⟨GStep.of_agree closed agree inner, ih⟩)
  | choice_r _ _ _ _ _ _ _ _ _ ih =>
      exact fun _ => collectedChoice_select (Or.inr ih)
  | var k _ _ _ _ _ _ _ ih =>
      intro p coll reg
      obtain ⟨i, spine, rfl⟩ := tailCollectR_ref_inv.mp coll
      obtain ⟨region, label⟩ := labels i (reg.2 i spine.mem_tailRefsR)
      obtain ⟨q, selected, source⟩ := ih _ label region
      exact ⟨q, select_spine spine selected, source⟩
  | seq_ok | recv | send | rcfg | par_l | par_r | left_merge | comm_merge_recv_send |
    comm_merge_send_recv | sync_recv_send | sync_send_recv | project | restrict =>
      intro p coll _
      rcases tailCollectR_image_shape coll with h | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h

private theorem collectedStep_complete
    (agree : ∀ i ∈ G.nodes, Q.label i = G.label i)
    (labels : ∀ i ∈ L, TailRegion G R L (G.label i) ∧
      tailCollectR G R (fresh G L) (G.label i) = some (Q.label (fresh G L i)))
    {p q : GProc} (sel : TailSelect G R p q)
    (step : GStep G ⟨q, pt, hl⟩ a ⟨dst, pt', hl'⟩) :
    ∀ out, tailCollectR G R (fresh G L) p = some out → TailRegion G R L p →
      GStep Q ⟨out, pt, hl⟩ a ⟨dst, pt', hl'⟩ := by
  induction sel with
  | packet _ ih => exact fun out coll region => ih step out coll region
  | left _ ih =>
      intro out coll region
      obtain ⟨l, r, hL, _, rfl⟩ := tailCollectR_choice_some_iff.mp coll
      exact .choice_l l r _ _ _ _ _ _ (ih step l hL (tailRegion_choice.mp region).1)
  | right _ ih =>
      intro out coll region
      obtain ⟨l, r, _, hR, rfl⟩ := tailCollectR_choice_some_iff.mp coll
      exact .choice_r l r _ _ _ _ _ _ (ih step r hR (tailRegion_choice.mp region).2)
  | @ref i _ _ ih =>
      intro out coll region
      cases coll
      obtain ⟨region', coll'⟩ := labels i (region.2 i (by simp [tailRefsR]))
      exact .var _ _ _ _ _ _ _ (ih step _ coll' region')
  | stop mem =>
      intro out coll region
      obtain ⟨r, _, rfl⟩ := (tailCollectR_rcfgPrefix_mem_some_iff mem).mp coll
      exact .choice_l _ r _ _ _ _ _ _ (GStep.of_agree G.closed (fun i hi => (agree i hi).symm)
        step ((tailRegion_rcfg mem).mp region).1)
  | next mem _ ih =>
      intro out coll region
      obtain ⟨r, coll', rfl⟩ := (tailCollectR_rcfgPrefix_mem_some_iff mem).mp coll
      exact .choice_r _ r _ _ _ _ _ _ (ih step r coll' ((tailRegion_rcfg mem).mp region))

end

/-- A nonempty execution of the collected tail starts in one original
selected continuation. Its endpoint and action word are preserved. -/
theorem graphTail_path_iff {G Q : ProcessGraph} {R : ReconfigSet}
    (h : graphTail G R = some Q) {a : Action} {w : List Action} {dst : GProc} :
    GraphPath Q Q.root (a :: w) dst ↔
      ∃ p, TailSelect G R G.root p ∧ GraphPath G p (a :: w) dst := by
  obtain ⟨L, root, entries, hRun, hRoot, hEntries, rfl⟩ := graphTail_some_inv h
  let out := tailGraphOf G R L root entries hRun hRoot hEntries
  have agree : ∀ i ∈ G.nodes, out.label i = G.label i :=
    fun _ hi => tailGraphOf_label_original hi
  have labels : ∀ i ∈ L, TailRegion G R L (G.label i) ∧
      tailCollectR G R (fresh G L) (G.label i) = some (out.label (fresh G L i)) := by
    intro i hi
    have hNode := (tailRun_root_success G R L hRun).2.2 i hi
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp
      ((collectTailLabels_some_iff _ L).mp ⟨entries, hEntries⟩ i hi)
    rw [tailGraphOf_label_fresh hi hp]
    exact ⟨⟨G.closed i hNode, (tailRun_root_refs_mem hRun).2 i hi⟩, hp⟩
  have region : TailRegion G R L G.root :=
    ⟨G.root_closed, (tailRun_root_refs_mem hRun).1⟩
  change GraphPath out root (a :: w) dst ↔ _
  simp only [GraphPath.cons_iff]
  constructor
  · rintro ⟨mid, first, rest⟩
    obtain ⟨p, selected, step⟩ := collectedStep_sound agree labels first _ hRoot region
    exact ⟨p, selected, mid, step, (GraphPath.agree agree (step.closed
      (select_closed selected G.root_closed))).mp rest⟩
  · rintro ⟨p, selected, mid, step, rest⟩
    exact ⟨mid, collectedStep_complete agree labels selected step _ hRoot region,
      (GraphPath.agree agree (step.closed (select_closed selected G.root_closed))).mpr rest⟩

end DyNetKAT.DyNetKAT
