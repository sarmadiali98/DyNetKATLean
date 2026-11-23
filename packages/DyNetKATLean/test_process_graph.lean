import DyNetKATLean

------------------------------------------------------------------------
-- Standalone tests for S6A - finite recursive process graphs and
-- operational correspondence (`DyNetKAT.DyNetKAT.ProcessGraph`).
--
-- Run with:  lake env lean test_process_graph.lean   (from lean/)
--
-- The ten required example classes are each demonstrated propositionally
-- (as theorems, not executable checks), including graph/SOS
-- correspondence instances.  No `sorry`, no new axioms; the principal
-- correspondence theorems are re-checked with `#print axioms` at the
-- bottom.
--
-- Example index (task §11):
--   1. A nonrecursive process.                          (ex1)
--   2. A single recursive variable.                     (ex2)
--   3. A self-referential guarded definition.           (ex3)
--   4. Two mutually recursive variables.                (ex4)
--   5. A recursive cycle containing packet processing.  (ex5)
--   6. A recursive cycle containing choice.             (ex6)
--   7. A zero-depth cutoff.                             (ex7)
--   8. A bounded execution traversing a cycle multiple times. (ex8)
--   9. An unguarded recursive definition.               (ex9)
--   10. A finite graph with an explicit back-edge, plus the
--       bounded-exploration-does-not-imply-bisimilarity witness. (ex10)
 ------------------------------------------------------------------------

 set_option linter.dupNamespace false

 namespace DyNetKAT.DyNetKAT.ProcessGraphTests

 open DyNetKAT.NetKAT

 ------------------------------------------------------------------------
 -- Fixtures
 ------------------------------------------------------------------------

 abbrev σ₀ : CtxPkt := examplePacket

 /-- A NetKAT field test used in the packet-processing cycle. -/
 abbrev pTest : NetKAT := NetKAT.fieldTest .port .v8

 /-- Membership in the two-variable support set. -/
 theorem mem_two {z : Var} (h : z = "X" ∨ z = "Y") :
     z ∈ ({ "X", "Y" } : Finset Var) := by
   simp only [Finset.mem_insert, Finset.mem_singleton]
   exact h

 /-- The singleton-membership side condition used by the support proofs. -/
 theorem sub_var_self {S : Finset Var} (h : "X" ∈ S) :
     recursiveVars (.var "X" : DyNetKAT) ⊆ S := by
   intro z hz
   simp only [recursiveVars, Finset.mem_singleton] at hz
   subst hz
   exact h

 ------------------------------------------------------------------------
 -- Example 1 - a nonrecursive process
 --
 -- `env` is empty and the process is variable-free, so the support set is
 -- empty and the graph has no nodes: the root is the plain translation.
 ------------------------------------------------------------------------

 def ex1Env : RecEnv := RecEnv.empty
 def ex1Proc : DyNetKAT := .nSeq NetKAT.id .deadlock
 theorem ex1_sup : FiniteSupport ex1Env ex1Proc ∅ := by
   constructor
   · intro x hx
     simp [recursiveVars, ex1Proc] at hx
   · intro x hx
     simp at hx

 def ex1Graph : ProcessGraph := toGraph ex1Env ex1Proc ∅ ex1_sup

 theorem ex1_root : ex1Graph.root = .nSeq NetKAT.id .deadlock := by
   simp [ex1Graph, toGraph, toGProc, ex1Proc]

 theorem ex1_corr : Corr ex1Graph ex1Env ex1Proc ex1Graph.root :=
   toGraph_corr ex1Env ex1Proc ∅ ex1_sup

 /-- Graph completeness in action: the SOS step of the nonrecursive
     process induces the corresponding graph step. -/
 theorem ex1_gstep (σ' : CtxPkt)
     (ev : HistorySemantics NetKAT.id (History.singleton σ₀)
       (History.singleton σ')) :
     ∃ gp' pt' hl',
       GStep ex1Graph
         { proc := ex1Graph.root, pending := [σ₀], handled := [] }
         (Action.packet σ₀ σ')
         { proc := gp', pending := pt', handled := hl' } ∧
       ∃ p', Corr ex1Graph ex1Env p' gp' := by
   refine (graph_step_iff ex1Graph ex1Env ex1Proc ex1Graph.root [σ₀] [] _
     ex1_corr).2 ⟨.deadlock, [], [σ'], ?_⟩
   exact Step.cpol_seq_ok NetKAT.id .deadlock σ₀ σ' [] [] ev

 /-- The concrete graph step, constructed directly. -/
 theorem ex1_gstep_direct (σ' : CtxPkt)
     (ev : HistorySemantics NetKAT.id (History.singleton σ₀)
       (History.singleton σ')) :
     GStep ex1Graph
       { proc := ex1Graph.root, pending := [σ₀], handled := [] }
       (Action.packet σ₀ σ')
       { proc := .deadlock, pending := [], handled := [σ'] } := by
   rw [ex1_root]
   exact GStep.seq_ok NetKAT.id .deadlock σ₀ σ' [] [] ev

 ------------------------------------------------------------------------
 -- Example 2 - a single recursive variable
 --
 -- `X ≜ id; ⊥`: one supported variable, one node, no cycle.
 ------------------------------------------------------------------------

 def ex2Env : RecEnv :=
   RecEnv.empty.define "X" (.nSeq NetKAT.id .deadlock)
 def ex2Proc : DyNetKAT := .var "X"
 def ex2Sup : Finset Var := {"X"}

 theorem ex2_lookup : ex2Env.lookup "X" = some (.nSeq NetKAT.id .deadlock) := by
   simp [ex2Env, RecEnv.lookup, RecEnv.define]

 theorem ex2_sup : FiniteSupport ex2Env ex2Proc ex2Sup := by
   constructor
   · exact sub_var_self (by simp [ex2Sup])
   · intro x hx
     simp only [ex2Sup, Finset.mem_singleton] at hx
     subst hx
     exact ⟨.nSeq NetKAT.id .deadlock, ex2_lookup, by
       intro z hz
       simp [recursiveVars] at hz⟩

 def ex2Graph : ProcessGraph := toGraph ex2Env ex2Proc ex2Sup ex2_sup

 theorem ex2_label : ex2Graph.label (varNode "X") = .nSeq NetKAT.id .deadlock := by
   simp [ex2Graph, ex2Sup, toGProc, ex2_lookup]

 theorem ex2_corr : Corr ex2Graph ex2Env ex2Proc ex2Graph.root :=
   toGraph_corr ex2Env ex2Proc ex2Sup ex2_sup

 /-- The variable reference is traversed as a graph edge: one `var` step
     onto the node label, then the prefix step. -/
 theorem ex2_gstep (σ' : CtxPkt)
     (ev : HistorySemantics NetKAT.id (History.singleton σ₀)
       (History.singleton σ')) :
     GStep ex2Graph
       { proc := ex2Graph.root, pending := [σ₀], handled := [] }
       (Action.packet σ₀ σ')
       { proc := .deadlock, pending := [], handled := [σ'] } :=
   GStep.var (varNode "X") .deadlock _ _ _ _ _
     (by rw [ex2_label]; exact GStep.seq_ok NetKAT.id .deadlock σ₀ σ' [] [] ev)

 ------------------------------------------------------------------------
 -- Example 3 (and 10) - a self-referential guarded definition with an
 -- explicit back-edge
 --
 -- `X ≜ id; X`: one node whose label contains a reference back to the
 -- node itself.  The graph is finite, closed, and cyclic.
 ------------------------------------------------------------------------

 def ex3Env : RecEnv :=
   RecEnv.empty.define "X" (.nSeq NetKAT.id (.var "X"))
 def ex3Proc : DyNetKAT := .var "X"
 def ex3Sup : Finset Var := {"X"}

 theorem ex3_lookup :
     ex3Env.lookup "X" = some (.nSeq NetKAT.id (.var "X")) := by
   simp [ex3Env, RecEnv.lookup, RecEnv.define]

 theorem ex3_sup : FiniteSupport ex3Env ex3Proc ex3Sup := by
   constructor
   · exact sub_var_self (by simp [ex3Sup])
   · intro x hx
     simp only [ex3Sup, Finset.mem_singleton] at hx
     subst hx
     exact ⟨.nSeq NetKAT.id (.var "X"), ex3_lookup, by
       intro z hz
       simpa [recursiveVars, ex3Sup] using hz⟩

 def ex3Graph : ProcessGraph := toGraph ex3Env ex3Proc ex3Sup ex3_sup

 theorem ex3_backedge :
     ex3Graph.label (varNode "X") = .nSeq NetKAT.id (GProc.ref (varNode "X")) := by
   simp [ex3Graph, ex3Sup, toGProc, ex3_lookup]

 theorem ex3_mem : varNode "X" ∈ ex3Graph.nodes := by
   simp [ex3Graph, toGraph, ex3Sup, varNode]

 theorem ex3_closed : gprocRefs (ex3Graph.label (varNode "X")) ⊆ ex3Graph.nodes := by
   rw [ex3_backedge]
   simp [gprocRefs, ex3_mem]

 theorem ex3_corr : Corr ex3Graph ex3Env ex3Proc ex3Graph.root :=
   toGraph_corr ex3Env ex3Proc ex3Sup ex3_sup

 ------------------------------------------------------------------------
 -- Example 4 - two mutually recursive variables
 --
 -- `X ≜ id; Y`, `Y ≜ id; X`: two nodes, two back-edges, one cycle.
 ------------------------------------------------------------------------

 def ex4Env : RecEnv :=
   (RecEnv.empty.define "X" (.nSeq NetKAT.id (.var "Y"))).define "Y"
     (.nSeq NetKAT.id (.var "X"))
 def ex4Proc : DyNetKAT := .var "X"
 def ex4Sup : Finset Var := {"X", "Y"}

 theorem ex4_lookupX :
     ex4Env.lookup "X" = some (.nSeq NetKAT.id (.var "Y")) := by
   simp [ex4Env, RecEnv.lookup, RecEnv.define]

 theorem ex4_lookupY :
     ex4Env.lookup "Y" = some (.nSeq NetKAT.id (.var "X")) := by
   simp [ex4Env, RecEnv.lookup, RecEnv.define]

 theorem ex4_supX : FiniteSupport ex4Env (.var "X") ex4Sup := by
   constructor
   · intro x hx
     simp only [recursiveVars, ex4Proc, Finset.mem_singleton] at hx
     exact mem_two (Or.inl hx)
   · intro x hx
     have hx' : x = "X" ∨ x = "Y" := by simpa [ex4Sup] using hx
     rcases hx' with rfl | rfl
     · exact ⟨.nSeq NetKAT.id (.var "Y"), ex4_lookupX, by
         intro z hz
         simp only [recursiveVars, Finset.mem_singleton] at hz
         exact mem_two (Or.inr hz)⟩
     · exact ⟨.nSeq NetKAT.id (.var "X"), ex4_lookupY, by
         intro z hz
         simp only [recursiveVars, Finset.mem_singleton] at hz
         exact mem_two (Or.inl hz)⟩

 theorem ex4_supY : FiniteSupport ex4Env (.var "Y") ex4Sup := by
   constructor
   · intro x hx
     simp only [recursiveVars, Finset.mem_singleton] at hx
     exact mem_two (Or.inr hx)
   · intro x hx
     have hx' : x = "X" ∨ x = "Y" := by simpa [ex4Sup] using hx
     rcases hx' with rfl | rfl
     · exact ⟨.nSeq NetKAT.id (.var "Y"), ex4_lookupX, by
         intro z hz
         simp only [recursiveVars, Finset.mem_singleton] at hz
         exact mem_two (Or.inr hz)⟩
     · exact ⟨.nSeq NetKAT.id (.var "X"), ex4_lookupY, by
         intro z hz
         simp only [recursiveVars, Finset.mem_singleton] at hz
         exact mem_two (Or.inl hz)⟩

 def ex4Graph : ProcessGraph := toGraph ex4Env ex4Proc ex4Sup ex4_supX

 theorem ex4_labelX :
     ex4Graph.label (varNode "X") = .nSeq NetKAT.id (GProc.ref (varNode "Y")) := by
   simp [ex4Graph, ex4Sup, toGProc, ex4_lookupX]

 theorem ex4_labelY :
     ex4Graph.label (varNode "Y") = .nSeq NetKAT.id (GProc.ref (varNode "X")) := by
   simp [ex4Graph, ex4Sup, toGProc, ex4_lookupY]

 theorem ex4_corr : Corr ex4Graph ex4Env ex4Proc ex4Graph.root :=
   toGraph_corr ex4Env ex4Proc ex4Sup ex4_supX

 /-- The finite cyclic bisimulation relating the two variable nodes. -/
 def ex4R : GProc → GProc → Prop :=
   fun a b =>
     (a = GProc.ref (varNode "X") ∧ b = GProc.ref (varNode "Y")) ∨
     (a = GProc.ref (varNode "Y") ∧ b = GProc.ref (varNode "X")) ∨
     a = b

 theorem ex4_isGBisimulation : IsGBisimulation ex4Graph ex4R := by
   constructor
   · intro a b h
     rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
     · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
     · exact Or.inl ⟨rfl, rfl⟩
     · exact Or.inr (Or.inr h.symm)
   · intro a b h pt hl act gp' pt' hl' hstep
     rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
     · have step := gstep_ref_inv hstep
       rw [ex4_labelX] at step
       obtain ⟨σ, σ', pt₀, hpt, ha, hgp, hpt', hhl, ev⟩ :=
         gstep_nSeq_inv step
       subst hpt; subst ha; subst hgp; subst hpt'; subst hhl
       exact ⟨GProc.ref (varNode "X"),
         GStep.var (varNode "Y") (GProc.ref (varNode "X")) _ _ _ _ _
           (by rw [ex4_labelY]
               exact GStep.seq_ok _ _ σ σ' _ _ ev),
         Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
     · have step := gstep_ref_inv hstep
       rw [ex4_labelY] at step
       obtain ⟨σ, σ', pt₀, hpt, ha, hgp, hpt', hhl, ev⟩ :=
         gstep_nSeq_inv step
       subst hpt; subst ha; subst hgp; subst hpt'; subst hhl
       exact ⟨GProc.ref (varNode "Y"),
         GStep.var (varNode "X") (GProc.ref (varNode "Y")) _ _ _ _ _
           (by rw [ex4_labelX]
               exact GStep.seq_ok _ _ σ σ' _ _ ev),
         Or.inl ⟨rfl, rfl⟩⟩
     · subst h
       exact ⟨gp', hstep, Or.inr (Or.inr rfl)⟩

 /-- **Unbounded payoff of the cyclic bisimulation**: the two mutually
     recursive variables are bisimilar in the original SOS - an unbounded
     result derived from a finite cyclic graph bisimulation. -/
 theorem ex4_mutually_bisimilar :
     Bisimilar ex4Env (.var "X") (.var "Y") := by
   apply gbisimilar_transfer ex4Graph ex4Env
     ⟨ex4R, ex4_isGBisimulation, Or.inl ⟨rfl, rfl⟩⟩
   · exact toGraph_corr ex4Env (.var "X") ex4Sup ex4_supX
   · exact toGraph_corr ex4Env (.var "Y") ex4Sup ex4_supY

 example : GBisimilar ex4Graph (.ref (varNode "X")) (.ref (varNode "Y")) :=
   (gbisimilar_iff_bisimilar ex4Graph ex4Env ex4_corr
     (toGraph_corr ex4Env (.var "Y") ex4Sup ex4_supY)).mpr ex4_mutually_bisimilar

 example : GBisimilar ex4Graph (.ref (varNode "X")) (.ref (varNode "X")) :=
   GBisimilar.trans ex4Graph
     ⟨ex4R, ex4_isGBisimulation, Or.inl ⟨rfl, rfl⟩⟩
     ⟨ex4R, ex4_isGBisimulation, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

 ------------------------------------------------------------------------
 -- Example 5 - a recursive cycle containing packet processing
 --
 -- `X ≜ (port = v8); X`: the cycle body performs a NetKAT packet step.
 ------------------------------------------------------------------------

 def ex5Env : RecEnv :=
   RecEnv.empty.define "X" (.nSeq pTest (.var "X"))
 def ex5Proc : DyNetKAT := .var "X"
 def ex5Sup : Finset Var := {"X"}

 theorem ex5_lookup :
     ex5Env.lookup "X" = some (.nSeq pTest (.var "X")) := by
   simp [ex5Env, RecEnv.lookup, RecEnv.define]

 theorem ex5_sup : FiniteSupport ex5Env ex5Proc ex5Sup := by
   constructor
   · exact sub_var_self (by simp [ex5Sup])
   · intro x hx
     simp only [ex5Sup, Finset.mem_singleton] at hx
     subst hx
     exact ⟨.nSeq pTest (.var "X"), ex5_lookup, by
       intro z hz
       simpa [recursiveVars, ex5Sup] using hz⟩

 def ex5Graph : ProcessGraph := toGraph ex5Env ex5Proc ex5Sup ex5_sup

 theorem ex5_label :
     ex5Graph.label (varNode "X") = .nSeq pTest (GProc.ref (varNode "X")) := by
   simp [ex5Graph, ex5Sup, toGProc, ex5_lookup]

 theorem ex5_corr : Corr ex5Graph ex5Env ex5Proc ex5Graph.root :=
   toGraph_corr ex5Env ex5Proc ex5Sup ex5_sup

 ------------------------------------------------------------------------
 -- Example 6 - a recursive cycle containing choice
 --
 -- `X ≜ (id; X) ⊕ ⊥`.
 ------------------------------------------------------------------------

 def ex6Env : RecEnv :=
   RecEnv.empty.define "X" (.choice (.nSeq NetKAT.id (.var "X")) .deadlock)
 def ex6Proc : DyNetKAT := .var "X"
 def ex6Sup : Finset Var := {"X"}

 theorem ex6_lookup :
     ex6Env.lookup "X" = some (.choice (.nSeq NetKAT.id (.var "X")) .deadlock) := by
   simp [ex6Env, RecEnv.lookup, RecEnv.define]

 theorem ex6_sup : FiniteSupport ex6Env ex6Proc ex6Sup := by
   constructor
   · exact sub_var_self (by simp [ex6Sup])
   · intro x hx
     simp only [ex6Sup, Finset.mem_singleton] at hx
     subst hx
     exact ⟨.choice (.nSeq NetKAT.id (.var "X")) .deadlock, ex6_lookup, by
       intro z hz
       simpa [recursiveVars, ex6Sup] using hz⟩

 def ex6Graph : ProcessGraph := toGraph ex6Env ex6Proc ex6Sup ex6_sup

 theorem ex6_label :
     ex6Graph.label (varNode "X") =
       .choice (.nSeq NetKAT.id (GProc.ref (varNode "X"))) .deadlock := by
   simp [ex6Graph, ex6Sup, toGProc, ex6_lookup]

 theorem ex6_corr : Corr ex6Graph ex6Env ex6Proc ex6Graph.root :=
   toGraph_corr ex6Env ex6Proc ex6Sup ex6_sup

 ------------------------------------------------------------------------
 -- Example 7 - the zero-depth cutoff
 --
 -- Zero-depth exploration identifies only the source configuration; it
 -- cannot observe any behavior (contrast with example 8).
 ------------------------------------------------------------------------

 theorem ex7_zero_cutoff (c c' : GConfig)
     (h : GReachableWithin ex3Graph 0 c c') : c = c' :=
   GReachableWithin.zero_eq h

 theorem ex7_zero_distinct :
     ¬ GReachableWithin ex3Graph 0
       { proc := GProc.ref (varNode "X"), pending := [σ₀], handled := [] }
       { proc := GProc.ref (varNode "X"), pending := [], handled := [σ₀] } := by
   intro h
   exact absurd (GReachableWithin.zero_eq h) (by simp)

 ------------------------------------------------------------------------
 -- Example 8 - a bounded execution traversing the cycle three times
 --
 -- With three pending packets, the self-loop `X ≜ id; X` executes the
 -- cycle once per packet; the graph execution and the SOS execution
 -- correspond step by step.
 ------------------------------------------------------------------------

 theorem ex8_three_cycle_steps (σ₁ σ₂ σ₃ : CtxPkt)
     (e1 : HistorySemantics NetKAT.id (History.singleton σ₁)
       (History.singleton σ₁))
     (e2 : HistorySemantics NetKAT.id (History.singleton σ₂)
       (History.singleton σ₂))
     (e3 : HistorySemantics NetKAT.id (History.singleton σ₃)
       (History.singleton σ₃)) :
     GSteps ex3Graph
       { proc := GProc.ref (varNode "X"),
         pending := [σ₁, σ₂, σ₃], handled := [] }
       [Action.packet σ₁ σ₁, Action.packet σ₂ σ₂, Action.packet σ₃ σ₃]
       { proc := GProc.ref (varNode "X"),
         pending := [], handled := [σ₃, σ₂, σ₁] } :=
   GSteps.cons _ _ _ _ _
     (GStep.var _ _ _ _ _ _ _
       (by rw [ex3_backedge]; exact GStep.seq_ok _ _ σ₁ σ₁ [σ₂, σ₃] [] e1))
     (GSteps.cons _ _ _ _ _
       (GStep.var _ _ _ _ _ _ _
         (by rw [ex3_backedge]; exact GStep.seq_ok _ _ σ₂ σ₂ [σ₃] [σ₁] e2))
       (GSteps.cons _ _ _ _ _
         (GStep.var _ _ _ _ _ _ _
           (by rw [ex3_backedge]; exact GStep.seq_ok _ _ σ₃ σ₃ [] [σ₂, σ₁] e3))
         (GSteps.nil _)))

 /-- The three-cycle graph execution lifts to a three-step SOS execution
     of the original recursive process (trace correspondence). -/
 theorem ex8_sos_trace (σ₁ σ₂ σ₃ : CtxPkt)
     (e1 : HistorySemantics NetKAT.id (History.singleton σ₁)
       (History.singleton σ₁))
     (e2 : HistorySemantics NetKAT.id (History.singleton σ₂)
       (History.singleton σ₂))
     (e3 : HistorySemantics NetKAT.id (History.singleton σ₃)
       (History.singleton σ₃)) :
     ∃ p',
       Steps ex3Env
         { proc := ex3Proc, pending := [σ₁, σ₂, σ₃], handled := [] }
         [Action.packet σ₁ σ₁, Action.packet σ₂ σ₂, Action.packet σ₃ σ₃]
         { proc := p', pending := [], handled := [σ₃, σ₂, σ₁] } ∧
       Corr ex3Graph ex3Env p' (GProc.ref (varNode "X")) :=
   gsteps_to_steps ex3Graph ex3Env
     { proc := GProc.ref (varNode "X"),
       pending := [σ₁, σ₂, σ₃], handled := [] }
     { proc := GProc.ref (varNode "X"),
       pending := [], handled := [σ₃, σ₂, σ₁] }
     _ (ex8_three_cycle_steps σ₁ σ₂ σ₃ e1 e2 e3) ex3Proc ex3_corr

 /-- The bounded execution is witnessed by `GReachableWithin 3`. -/
 theorem ex8_reachable_within (σ₁ σ₂ σ₃ : CtxPkt)
     (e1 : HistorySemantics NetKAT.id (History.singleton σ₁)
       (History.singleton σ₁))
     (e2 : HistorySemantics NetKAT.id (History.singleton σ₂)
       (History.singleton σ₂))
     (e3 : HistorySemantics NetKAT.id (History.singleton σ₃)
       (History.singleton σ₃)) :
     GReachableWithin ex3Graph 3
       { proc := GProc.ref (varNode "X"),
         pending := [σ₁, σ₂, σ₃], handled := [] }
       { proc := GProc.ref (varNode "X"),
         pending := [], handled := [σ₃, σ₂, σ₁] } :=
   gsteps_reachable_within (ex8_three_cycle_steps σ₁ σ₂ σ₃ e1 e2 e3) 3
     (by simp)

 ------------------------------------------------------------------------
 -- Example 9 - an unguarded recursive definition
 --
 -- `X ≜ Y`, `Y ≜ X`: both the SOS and the graph are stuck - no
 -- transition exists on either side (proved by induction on the
 -- transition derivation).  The graph still constructs: guardedness is
 -- NOT required for the finite-support construction.
 ------------------------------------------------------------------------

 def ex9Env : RecEnv :=
   (RecEnv.empty.define "X" (.var "Y")).define "Y" (.var "X")
 def ex9Proc : DyNetKAT := .var "X"
 def ex9Sup : Finset Var := {"X", "Y"}

 theorem ex9_lookupX : ex9Env.lookup "X" = some (.var "Y") := by
   simp [ex9Env, RecEnv.lookup, RecEnv.define]

 theorem ex9_lookupY : ex9Env.lookup "Y" = some (.var "X") := by
   simp [ex9Env, RecEnv.lookup, RecEnv.define]

 theorem ex9_sup : FiniteSupport ex9Env ex9Proc ex9Sup := by
   constructor
   · intro x hx
     simp only [recursiveVars, ex9Proc, Finset.mem_singleton] at hx
     exact mem_two (Or.inl hx)
   · intro x hx
     have hx' : x = "X" ∨ x = "Y" := by simpa [ex9Sup] using hx
     rcases hx' with rfl | rfl
     · exact ⟨.var "Y", ex9_lookupX, by
         intro z hz
         simp only [recursiveVars, Finset.mem_singleton] at hz
         exact mem_two (Or.inr hz)⟩
     · exact ⟨.var "X", ex9_lookupY, by
         intro z hz
         simp only [recursiveVars, Finset.mem_singleton] at hz
         exact mem_two (Or.inl hz)⟩

 def ex9Graph : ProcessGraph := toGraph ex9Env ex9Proc ex9Sup ex9_sup

 theorem ex9_labelX : ex9Graph.label (varNode "X") = GProc.ref (varNode "Y") := by
   simp [ex9Graph, ex9Sup, toGProc, ex9_lookupX]

 theorem ex9_labelY : ex9Graph.label (varNode "Y") = GProc.ref (varNode "X") := by
   simp [ex9Graph, ex9Sup, toGProc, ex9_lookupY]

 theorem ex9_sos_stuck (pt hl : List CtxPkt) (a : Action) (dst : Config) :
     ¬ Step ex9Env
       { proc := .var "X", pending := pt, handled := hl } a dst :=
   no_step_var_two_cycle ex9Env "X" "Y" ex9_lookupX ex9_lookupY pt hl a dst

 theorem ex9_graph_stuck (pt hl : List CtxPkt) (a : Action) (dst : GConfig) :
     ¬ GStep ex9Graph
       { proc := GProc.ref (varNode "X"), pending := pt, handled := hl } a dst :=
   no_gstep_ref_two_cycle ex9Graph (varNode "X") (varNode "Y") ex9_labelX
     ex9_labelY pt hl a dst

 ------------------------------------------------------------------------
 -- Example 10 - a finite graph with explicit back-edges, and the
 -- bounded/unbounded distinction
 --
 -- One graph with two nodes: an infinite self-loop (back-edge to itself)
 -- and a two-step chain.  The two configurations agree on the first two
 -- executed actions but are NOT graph-bisimilar: with three pending
 -- packets the loop performs a third step that the chain cannot match.
 -- This is the graph-level counterpart of `not_bisimilar_cutoff`: a
 -- finite-depth cutoff never establishes unbounded bisimulation.
 ------------------------------------------------------------------------

 def ex10Label : NodeId → GProc
   | Sum.inr 0 => .nSeq NetKAT.id (GProc.ref (Sum.inr 0))
   | Sum.inr 1 => .nSeq NetKAT.id (.nSeq NetKAT.id .deadlock)
   | _ => .deadlock

 theorem ex10_label0 :
     ex10Label (auxNode 0) = .nSeq NetKAT.id (GProc.ref (auxNode 0)) := rfl

 theorem ex10_label1 :
     ex10Label (auxNode 1) =
       .nSeq NetKAT.id (.nSeq NetKAT.id .deadlock) := rfl

 def ex10Graph : ProcessGraph :=
   ProcessGraph.mk
     ({auxNode 0, auxNode 1} : Finset NodeId)
     (GProc.ref (auxNode 0))
     ex10Label
     (by simp [gprocRefs, auxNode])
     (by
       intro i hi
       have hi2 : i ∈ ({auxNode 0, auxNode 1} : Finset NodeId) := hi
       have hi' : i = auxNode 0 ∨ i = auxNode 1 := by
         simpa [auxNode] using hi2
       rcases hi' with rfl | rfl
       · show gprocRefs (ex10Label (auxNode 0)) ⊆
           ({auxNode 0, auxNode 1} : Finset NodeId)
         rw [ex10_label0]
         simp [gprocRefs]
       · show gprocRefs (ex10Label (auxNode 1)) ⊆
           ({auxNode 0, auxNode 1} : Finset NodeId)
         rw [ex10_label1]
         simp [gprocRefs])

 theorem ex10Graph_label : ProcessGraph.label ex10Graph = ex10Label := rfl

 theorem ex10_agree_depth2 (σ : CtxPkt)
     (e1 : HistorySemantics NetKAT.id (History.singleton σ)
       (History.singleton σ))
     (e2 : HistorySemantics NetKAT.id (History.singleton σ)
       (History.singleton σ)) :
     GReachableWithin ex10Graph 2
       { proc := GProc.ref (auxNode 0), pending := [σ, σ, σ], handled := [] }
       { proc := GProc.ref (auxNode 0), pending := [σ], handled := [σ, σ] } ∧
     GReachableWithin ex10Graph 2
       { proc := GProc.ref (auxNode 1), pending := [σ, σ, σ], handled := [] }
       { proc := .deadlock, pending := [σ], handled := [σ, σ] } := by
   constructor
   · refine GReachableWithin.step 1 _ _ _ _
       (GStep.var (auxNode 0) (GProc.ref (auxNode 0)) (Action.packet σ σ)
         [σ, σ, σ] [σ, σ] [] [σ]
         (by rw [ex10Graph_label, ex10_label0]
             exact GStep.seq_ok _ _ σ σ [σ, σ] [] e1))
       (GReachableWithin.step 0 _ _ _ _
         (GStep.var (auxNode 0) (GProc.ref (auxNode 0)) (Action.packet σ σ)
           [σ, σ] [σ] [σ] [σ, σ]
           (by rw [ex10Graph_label, ex10_label0]
               exact GStep.seq_ok _ _ σ σ [σ] [σ] e1))
         (GReachableWithin.refl _ _))
   · refine GReachableWithin.step 1 _ _ _ _
       (GStep.var (auxNode 1) (GProc.nSeq NetKAT.id GProc.deadlock)
         (Action.packet σ σ) [σ, σ, σ] [σ, σ] [] [σ]
         (by rw [ex10Graph_label, ex10_label1]
             exact GStep.seq_ok _ _ σ σ [σ, σ] [] e1))
       (GReachableWithin.step 0 _ _ _ _
         (GStep.seq_ok _ _ σ σ [σ] [σ] e2)
         (GReachableWithin.refl _ _))

 theorem ex10_not_gbisimilar (σ : CtxPkt)
     (e1 : HistorySemantics NetKAT.id (History.singleton σ)
       (History.singleton σ))
     (e2 : HistorySemantics NetKAT.id (History.singleton σ)
       (History.singleton σ))
     (e3 : HistorySemantics NetKAT.id (History.singleton σ)
       (History.singleton σ)) :
     ¬ GBisimilar ex10Graph
       (GProc.ref (auxNode 0)) (GProc.ref (auxNode 1)) := by
   rintro ⟨R, hR, hR01⟩
   obtain ⟨hRsym, hRmatch⟩ := hR
   -- three loop steps from the self-loop node
   have s1 : GStep ex10Graph
       { proc := GProc.ref (auxNode 0), pending := [σ, σ, σ], handled := [] }
       (Action.packet σ σ)
       { proc := GProc.ref (auxNode 0), pending := [σ, σ], handled := [σ] } :=
     GStep.var _ _ _ _ _ _ _
       (by rw [ex10Graph_label, ex10_label0]; exact GStep.seq_ok _ _ σ σ [σ, σ] [] e1)
   have s2 : GStep ex10Graph
       { proc := GProc.ref (auxNode 0), pending := [σ, σ], handled := [σ] }
       (Action.packet σ σ)
       { proc := GProc.ref (auxNode 0), pending := [σ], handled := [σ, σ] } :=
     GStep.var _ _ _ _ _ _ _
       (by rw [ex10Graph_label, ex10_label0]; exact GStep.seq_ok _ _ σ σ [σ] [σ] e2)
   have s3 : GStep ex10Graph
       { proc := GProc.ref (auxNode 0), pending := [σ], handled := [σ, σ] }
       (Action.packet σ σ)
       { proc := GProc.ref (auxNode 0), pending := [], handled := [σ, σ, σ] } :=
     GStep.var _ _ _ _ _ _ _
       (by rw [ex10Graph_label, ex10_label0]; exact GStep.seq_ok _ _ σ σ [] [σ, σ] e3)
   -- round 1: the chain's only step lands on `id; ⊥`
   obtain ⟨w1, hw1, hR1⟩ := hRmatch _ _ hR01 _ _ _ _ _ _ s1
   have step1 := gstep_ref_inv hw1
   rw [ex10Graph_label, ex10_label1] at step1
   obtain ⟨σ₁, σ₂, pt₁, hpt, ha, hgp, hpt', hhl, ev⟩ := gstep_nSeq_inv step1
   subst hgp
   -- round 2: the chain's second step lands on `⊥`
   obtain ⟨w2, hw2, hR2⟩ := hRmatch _ _ hR1 _ _ _ _ _ _ s2
   have step2 := gstep_nSeq_inv hw2
   obtain ⟨σ₃, σ₄, pt₂, hpt2, ha2, hgp2, hpt2', hhl2, ev2⟩ := step2
   subst hgp2
   -- round 3: the chain is dead; the loop still steps
   obtain ⟨w3, hw3, _⟩ := hRmatch _ _ hR2 _ _ _ _ _ _ s3
   cases hw3

 ------------------------------------------------------------------------
 -- The principal correspondence theorems, re-checked for their axiom
 -- footprint (expect only the standard Mathlib axioms, no `sorryAx`).
 ------------------------------------------------------------------------

 #print axioms graph_step_iff
 #print axioms gstep_to_step
 #print axioms step_to_gstep
 #print axioms toGraph_corr
 #print axioms gbisimilar_transfer
 #print axioms graph_bisimulation_environment_independent
 #print axioms gbisimilar_transfer2
 #print axioms infEnv_no_finite_support
 #print axioms steps_project_lift
 #print axioms steps_project_unwrap

 end DyNetKAT.DyNetKAT.ProcessGraphTests
