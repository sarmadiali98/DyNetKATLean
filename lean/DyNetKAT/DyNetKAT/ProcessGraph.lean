------------------------------------------------------------------------
-- S6A — Finite recursive process graphs and operational correspondence
--
-- Paper grounding (DyNetKAT paper, arXiv:2102.10035v4):
--   * Eq. (1), p. 8 — DyNetKAT syntax with recursive variables `X`, each
--     with a unique defining equation `X ≜ d` (§II-C).
--   * Fig. 8, rule `(cpolX)` — a recursive variable defined as `X ≜ p`
--     behaves according to `p`; rendered in Lean as `Step.cpol_var`
--     (`Semantics.lean`), which requires `env.lookup name = some body`.
--   * Definition 7 (p. 13) — guardedness of variable occurrences.
--   * The paper itself contains NO graph representation; the finite
--     cyclic-graph representation below follows the authors' guidance:
--     ordinary process constructs stay in the term structure, recursive
--     variables become edges (`GProc.ref`) into a finite node set, and
--     recursive definitions produce cycles — without infinite unfolding.
--
-- What this module establishes:
--   1. `GProc` — the DyNetKAT AST with recursive variables replaced by
--      node references, and `ProcessGraph` — a finite node set with a
--      labeling whose references are all live (`closed`, `root_closed`).
--   2. `GStep` — the graph-level Figure 8 semantics over configurations
--      carrying the full packet state (pending and handled histories);
--      recursive-variable lookup is edge traversal (`GStep.var`), never
--      a syntactic copy of the definition.
--   3. `Corr` — the process/graph correspondence, defined as membership
--      in a correspondence-closed relation (greatest-fixpoint style, so
--      that cyclic definitions are handled without unfolding).
--   4. Soundness and completeness of the graph semantics w.r.t. the
--      environment-indexed SOS (`gstep_to_step`, `step_to_gstep`) and
--      the combined iff (`graph_step_iff`).
--   5. `toGraph` — constructive graph construction from a `RecEnv` under
--      an explicit finite-support assumption (`FiniteSupport`); the
--      construction uses no choice principles.  A concrete environment
--      with infinitely many reachable definitions (`infEnv`) is proved
--      to admit no finite support for this label-preserving compiler.
--   6. Bounded exploration (`GReachableWithin`, `GSteps`) with
--      monotonicity, the zero-depth cutoff, and composition; the
--      correspondence of bounded graph exploration with finite SOS
--      execution traces (`gsteps_to_steps`, `steps_to_gsteps`) and the
--      bridge to the paper's projection `π_n`
--      (`steps_project_lift`, `steps_project_unwrap`).
--   7. Cyclic graph bisimulation (`IsGBisimulation`, `GBisimilar`) and
--      the unbounded transfer theorem: a graph bisimulation
--      between corresponding processes yields genuine unbounded
--      `Bisimilar env` (`gbisimilar_transfer`), for every environment
--      under which the correspondence holds
--      (`graph_bisimulation_environment_independent`), including two
--      different environments (`IsBisimulation2`, `gbisimilar_transfer2`).
--
-- Deliberately OUT of scope (mathematical obligations, not assumptions):
--   - the full end-to-end recursive safety checker (later milestone),
--   - AIP soundness (Lemma 11) and Lemma 8 branching finiteness,
--   - a cutoff theorem turning bounded exploration into unbounded
--     verdicts: bounded agreement never implies unbounded bisimilarity
--     (see `not_gbisimilar_cutoff_pair` for the graph-level witness).
------------------------------------------------------------------------

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.String.Basic
import DyNetKAT.NetKAT.Packet
import DyNetKAT.NetKAT.HistorySemantics
import DyNetKAT.DyNetKAT.AST
import DyNetKAT.DyNetKAT.Action
import DyNetKAT.DyNetKAT.Config
import DyNetKAT.DyNetKAT.RecEnv
import DyNetKAT.DyNetKAT.Semantics
import DyNetKAT.DyNetKAT.Bisimulation
import DyNetKAT.DyNetKAT.Definedness
import DyNetKAT.DyNetKAT.RestrictionProjection

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : PacketSchema}

open DyNetKAT.NetKAT

------------------------------------------------------------------------
-- §1 Graph-level process terms and node identifiers
------------------------------------------------------------------------

/-- Node identifiers.  `Sum.inl x` is the canonical node for the recursive
    variable `x` (used by `toGraph`); `Sum.inr k` is a spare namespace for
    synthetic graphs.  `Var = String` has no injection into `Nat` in the
    library, so the disjoint sum keeps `varNode` injective by construction. -/
abbrev NodeId : Type := String ⊕ Nat

/-- The canonical node of a recursive variable. -/
def varNode (x : Var) : NodeId := Sum.inl x

/-- An auxiliary node (unused by `toGraph`). -/
def auxNode (k : Nat) : NodeId := Sum.inr k

/-- Graph-level process terms: the DyNetKAT AST (Eq. 1 + Eq. 6) with
    recursive variables replaced by node references.  Everything else is
    carried verbatim, including the NetKAT policies, channels,
    restriction sets, projection budgets and the full constructor
    structure, so that the graph semantics can mirror Figure 8 exactly. -/
inductive GProc (schema : PacketSchema := ctxSchema) : Type
  | deadlock                                                  -- ⊥
  | nSeq : NetKAT schema → GProc schema → (GProc schema)                             -- N;D
  | recv : Channel → NetKAT schema → GProc schema → (GProc schema)                   -- x?N;D
  | send : Channel → NetKAT schema → GProc schema → (GProc schema)                   -- x!N;D
  | rcfgPrefix : Channel → NetKAT schema → GProc schema → (GProc schema)             -- rcfg_{x,N};D
  | parallel : GProc schema → GProc schema → (GProc schema)                          -- D‖D
  | choice : GProc schema → GProc schema → (GProc schema)                            -- D⊕D
  | leftMerge : GProc schema → GProc schema → (GProc schema)                         -- D⌊⌊D
  | commMerge : GProc schema → GProc schema → (GProc schema)                         -- D|D
  | restrict : Set (CommunicationAction schema) → GProc schema → (GProc schema)        -- δ_ℒ(D)
  | project : Nat → GProc schema → (GProc schema)                             -- π_n(D)
  | ref : NodeId → (GProc schema)                                      -- variable edge

/-- The node references occurring in a graph-level process term. -/
def gprocRefs : GProc schema → Finset NodeId
  | .deadlock => ∅
  | .nSeq _ c => gprocRefs c
  | .recv _ _ c => gprocRefs c
  | .send _ _ c => gprocRefs c
  | .rcfgPrefix _ _ c => gprocRefs c
  | .parallel a b => gprocRefs a ∪ gprocRefs b
  | .choice a b => gprocRefs a ∪ gprocRefs b
  | .leftMerge a b => gprocRefs a ∪ gprocRefs b
  | .commMerge a b => gprocRefs a ∪ gprocRefs b
  | .restrict _ c => gprocRefs c
  | .project _ c => gprocRefs c
  | .ref i => {i}

------------------------------------------------------------------------
-- §2 The finite process graph
------------------------------------------------------------------------

/-- A finite recursive process graph.

    * `nodes` is finite: the graph is a finite representation.
    * `root` is the graph image of the original process.
    * `label` gives the defining term of each node; recursive-variable
      references inside labels are `GProc.ref` edges, so recursive
      definitions produce cycles without infinite unfolding.
    * `root_closed` and `closed` say that every referenced node belongs
      to the graph (property 4 of the representation contract). -/
structure ProcessGraph (schema : PacketSchema := ctxSchema) where
  nodes : Finset NodeId
  root : GProc schema
  label : NodeId → GProc schema
  root_closed : gprocRefs root ⊆ nodes
  closed : ∀ i ∈ nodes, gprocRefs (label i) ⊆ nodes

/-- Graph-level configuration: the process component is a graph term,
    and both packet histories are preserved (Figure 8 configurations
    `(d, H, H')`). -/
structure GConfig (schema : PacketSchema := ctxSchema) where
  proc : GProc schema
  pending : List schema.Packet
  handled : List schema.Packet

------------------------------------------------------------------------
-- §3 Graph operational semantics (mirror of Figure 8 / `Step`)
------------------------------------------------------------------------

/-- The graph-level small-step relation, mirroring `Step env` constructor
    by constructor with the process component taken from `GProc`.
    The `(cpolX)` rule becomes edge traversal: a step of `.ref i` is a
    step of the node label `G.label i` — the definition is followed, not
    copied into the syntax. -/
inductive GStep {schema : PacketSchema} (G : ProcessGraph schema) : GConfig schema → Action schema → GConfig schema → Prop
  | seq_ok (N : NetKAT schema) (cont : GProc schema) (σ σ' : schema.Packet) (pt hl : List schema.Packet)
      (evaluates : HistorySemantics N (History.singleton σ) (History.singleton σ')) :
      GStep G
        (show (GConfig schema) from
          { proc := .nSeq N cont, pending := σ :: pt, handled := hl })
        (show (Action schema) from Action.packet σ σ')
        (show (GConfig schema) from
          { proc := cont, pending := pt, handled := σ' :: hl })

  | choice_l (gp gq gp' : GProc schema) (a : Action schema) (pt pt' hl hl' : List schema.Packet)
      (steps : GStep G
        (show (GConfig schema) from { proc := gp, pending := pt, handled := hl })
        a
        (show (GConfig schema) from { proc := gp', pending := pt', handled := hl' })) :
      GStep G
        (show (GConfig schema) from { proc := .choice gp gq, pending := pt, handled := hl })
        a
        (show (GConfig schema) from { proc := gp', pending := pt', handled := hl' })

  | choice_r (gp gq gq' : GProc schema) (a : Action schema) (pt pt' hl hl' : List schema.Packet)
      (steps : GStep G
        (show (GConfig schema) from { proc := gq, pending := pt, handled := hl })
        a
        (show (GConfig schema) from { proc := gq', pending := pt', handled := hl' })) :
      GStep G
        (show (GConfig schema) from { proc := .choice gp gq, pending := pt, handled := hl })
        a
        (show (GConfig schema) from { proc := gq', pending := pt', handled := hl' })

  | par_l (gp gq gp' : GProc schema) (a : Action schema) (pt pt' hl hl' : List schema.Packet)
      (steps : GStep G
        (show (GConfig schema) from { proc := gp, pending := pt, handled := hl })
        a
        (show (GConfig schema) from { proc := gp', pending := pt', handled := hl' })) :
      GStep G
        (show (GConfig schema) from { proc := .parallel gp gq, pending := pt, handled := hl })
        a
        (show (GConfig schema) from
          { proc := .parallel gp' gq, pending := pt', handled := hl' })

  | par_r (gp gq gq' : GProc schema) (a : Action schema) (pt pt' hl hl' : List schema.Packet)
      (steps : GStep G
        (show (GConfig schema) from { proc := gq, pending := pt, handled := hl })
        a
        (show (GConfig schema) from { proc := gq', pending := pt', handled := hl' })) :
      GStep G
        (show (GConfig schema) from { proc := .parallel gp gq, pending := pt, handled := hl })
        a
        (show (GConfig schema) from
          { proc := .parallel gp gq', pending := pt', handled := hl' })

  | left_merge (gp gq gp' : GProc schema) (a : Action schema) (pt pt' hl hl' : List schema.Packet)
      (steps : GStep G
        (show (GConfig schema) from { proc := gp, pending := pt, handled := hl })
        a
        (show (GConfig schema) from { proc := gp', pending := pt', handled := hl' })) :
      GStep G
        (show (GConfig schema) from { proc := .leftMerge gp gq, pending := pt, handled := hl })
        a
        (show (GConfig schema) from
          { proc := .parallel gp' gq, pending := pt', handled := hl' })

  | comm_merge_recv_send (x : Channel) (r : NetKAT schema) (gp gs gp' gs' : GProc schema)
      (pt hl : List schema.Packet)
      (recv_step : GStep G
        (show (GConfig schema) from { proc := gp, pending := pt, handled := hl })
        (show (Action schema) from Action.recv x r)
        (show (GConfig schema) from { proc := gp', pending := pt, handled := hl }))
      (send_step : GStep G
        (show (GConfig schema) from { proc := gs, pending := pt, handled := hl })
        (show (Action schema) from Action.send x r)
        (show (GConfig schema) from { proc := gs', pending := pt, handled := hl })) :
      GStep G
        (show (GConfig schema) from { proc := .commMerge gp gs, pending := pt, handled := hl })
        (show (Action schema) from Action.rcfg x r)
        (show (GConfig schema) from
          { proc := .parallel gp' gs', pending := pt, handled := hl })

  | comm_merge_send_recv (x : Channel) (r : NetKAT schema) (gp gs gp' gs' : GProc schema)
      (pt hl : List schema.Packet)
      (send_step : GStep G
        (show (GConfig schema) from { proc := gp, pending := pt, handled := hl })
        (show (Action schema) from Action.send x r)
        (show (GConfig schema) from { proc := gp', pending := pt, handled := hl }))
      (recv_step : GStep G
        (show (GConfig schema) from { proc := gs, pending := pt, handled := hl })
        (show (Action schema) from Action.recv x r)
        (show (GConfig schema) from { proc := gs', pending := pt, handled := hl })) :
      GStep G
        (show (GConfig schema) from { proc := .commMerge gp gs, pending := pt, handled := hl })
        (show (Action schema) from Action.rcfg x r)
        (show (GConfig schema) from
          { proc := .parallel gp' gs', pending := pt, handled := hl })

  | recv (x : Channel) (N : NetKAT schema) (cont : GProc schema) (pt hl : List schema.Packet) :
      GStep G
        (show (GConfig schema) from { proc := .recv x N cont, pending := pt, handled := hl })
        (show (Action schema) from Action.recv x N)
        (show (GConfig schema) from { proc := cont, pending := pt, handled := hl })

  | send (x : Channel) (N : NetKAT schema) (cont : GProc schema) (pt hl : List schema.Packet) :
      GStep G
        (show (GConfig schema) from { proc := .send x N cont, pending := pt, handled := hl })
        (show (Action schema) from Action.send x N)
        (show (GConfig schema) from { proc := cont, pending := pt, handled := hl })

  | rcfg (x : Channel) (N : NetKAT schema) (cont : GProc schema) (pt hl : List schema.Packet) :
      GStep G
        (show (GConfig schema) from
          { proc := .rcfgPrefix x N cont, pending := pt, handled := hl })
        (show (Action schema) from Action.rcfg x N)
        (show (GConfig schema) from { proc := cont, pending := pt, handled := hl })

  | var (i : NodeId) (gp' : GProc schema) (a : Action schema) (pt pt' hl hl' : List schema.Packet)
      (step : GStep G
        (show (GConfig schema) from { proc := G.label i, pending := pt, handled := hl })
        a
        (show (GConfig schema) from { proc := gp', pending := pt', handled := hl' })) :
      GStep G
        (show (GConfig schema) from { proc := .ref i, pending := pt, handled := hl })
        a
        (show (GConfig schema) from { proc := gp', pending := pt', handled := hl' })

  | sync_recv_send (x : Channel) (r : NetKAT schema) (gp gs gp' gs' : GProc schema)
      (pt hl : List schema.Packet)
      (recv_step : GStep G
        (show (GConfig schema) from { proc := gp, pending := pt, handled := hl })
        (show (Action schema) from Action.recv x r)
        (show (GConfig schema) from { proc := gp', pending := pt, handled := hl }))
      (send_step : GStep G
        (show (GConfig schema) from { proc := gs, pending := pt, handled := hl })
        (show (Action schema) from Action.send x r)
        (show (GConfig schema) from { proc := gs', pending := pt, handled := hl })) :
      GStep G
        (show (GConfig schema) from { proc := .parallel gp gs, pending := pt, handled := hl })
        (show (Action schema) from Action.rcfg x r)
        (show (GConfig schema) from
          { proc := .parallel gp' gs', pending := pt, handled := hl })

  | sync_send_recv (x : Channel) (r : NetKAT schema) (gp gs gp' gs' : GProc schema)
      (pt hl : List schema.Packet)
      (send_step : GStep G
        (show (GConfig schema) from { proc := gp, pending := pt, handled := hl })
        (show (Action schema) from Action.send x r)
        (show (GConfig schema) from { proc := gp', pending := pt, handled := hl }))
      (recv_step : GStep G
        (show (GConfig schema) from { proc := gs, pending := pt, handled := hl })
        (show (Action schema) from Action.recv x r)
        (show (GConfig schema) from { proc := gs', pending := pt, handled := hl })) :
      GStep G
        (show (GConfig schema) from { proc := .parallel gp gs, pending := pt, handled := hl })
        (show (Action schema) from Action.rcfg x r)
        (show (GConfig schema) from
          { proc := .parallel gp' gs', pending := pt, handled := hl })

  | project (n : Nat) (gp gp' : GProc schema) (a : Action schema) (pt pt' hl hl' : List schema.Packet)
      (step : GStep G
        (show (GConfig schema) from { proc := gp, pending := pt, handled := hl })
        a
        (show (GConfig schema) from { proc := gp', pending := pt', handled := hl' })) :
      GStep G
        (show (GConfig schema) from
          { proc := .project (n + 1) gp, pending := pt, handled := hl })
        a
        (show (GConfig schema) from
          { proc := .project n gp', pending := pt', handled := hl' })

  | restrict (L : Set (CommunicationAction schema)) (gp gp' : GProc schema) (a : Action schema)
      (pt pt' hl hl' : List schema.Packet)
      (allowed : actionAllowed L a)
      (step : GStep G
        (show (GConfig schema) from { proc := gp, pending := pt, handled := hl })
        a
        (show (GConfig schema) from { proc := gp', pending := pt', handled := hl' })) :
      GStep G
        (show (GConfig schema) from { proc := .restrict L gp, pending := pt, handled := hl })
        a
        (show (GConfig schema) from
          { proc := .restrict L gp', pending := pt', handled := hl' })

------------------------------------------------------------------------
/-- A transition of a closed graph term remains within the graph's node set. -/
theorem GStep.closed {G : ProcessGraph schema} {src dst : GConfig schema} {a : Action schema}
    (step : GStep G src a dst) :
    gprocRefs src.proc ⊆ G.nodes → gprocRefs dst.proc ⊆ G.nodes := by
  induction step with
  | seq_ok | recv | send | rcfg => exact id
  | restrict _ _ _ _ _ _ _ _ _ _ ih | project _ _ _ _ _ _ _ _ _ ih => exact ih
  | choice_l _ _ _ _ _ _ _ _ _ ih =>
      exact fun h => ih (Finset.union_subset_iff.mp h).1
  | choice_r _ _ _ _ _ _ _ _ _ ih =>
      exact fun h => ih (Finset.union_subset_iff.mp h).2
  | par_l _ _ _ _ _ _ _ _ _ ih | left_merge _ _ _ _ _ _ _ _ _ ih =>
      exact fun h => Finset.union_subset_iff.mpr
        ⟨ih (Finset.union_subset_iff.mp h).1, (Finset.union_subset_iff.mp h).2⟩
  | par_r _ _ _ _ _ _ _ _ _ ih =>
      exact fun h => Finset.union_subset_iff.mpr
        ⟨(Finset.union_subset_iff.mp h).1, ih (Finset.union_subset_iff.mp h).2⟩
  | sync_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ |
    sync_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ |
    comm_merge_recv_send _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ |
    comm_merge_send_recv _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact fun h => Finset.union_subset_iff.mpr
        ⟨ih₁ (Finset.union_subset_iff.mp h).1, ih₂ (Finset.union_subset_iff.mp h).2⟩
  | var i _ _ _ _ _ _ _ ih =>
      exact fun h => ih (G.closed i (h (Finset.mem_singleton_self i)))

------------------------------------------------------------------------
-- §4 The process/graph correspondence
--
-- `Corr` is defined greatest-fixpoint style: `p` corresponds to `gp`
-- when some relation `S` contains the pair and is closed under the
-- structural conditions below.  Closure is required in both directions
-- (`IsCorrespondenceB` destructs on the process shape, giving the
-- graph shape and the component correspondences; `IsCorrespondenceF`
-- destructs on the graph shape, giving the process shape and the
-- component correspondences), so that both proof directions can invert
-- a correspondence hypothesis on its concrete side.  The var case is
-- deliberately unrolled through the node label, which makes cyclic
-- definitions (e.g. `X ≜ id;X`) correspondences with *finite* closed
-- witnesses — no unfolding, no induction on the chain.
------------------------------------------------------------------------

/-- The closure condition, destructing on the process shape: for every
    pair in `S`, the process shape determines the graph shape and the
    component pairs must again lie in `S`.  The `var` arm unrolls through
    the node label, which is what makes cyclic definitions correspond
    with finite closed witnesses. -/
def CorrBArm (G : ProcessGraph schema) (env : RecEnv schema) (S : DyNetKAT schema → GProc schema → Prop)
    (p : DyNetKAT schema) (gp : GProc schema) : Prop :=
  match p with
  | .deadlock => gp = .deadlock
  | .nSeq N p₀ => ∃ gp₀, gp = .nSeq N gp₀ ∧ S p₀ gp₀
  | .recv x N p₀ => ∃ gp₀, gp = .recv x N gp₀ ∧ S p₀ gp₀
  | .send x N p₀ => ∃ gp₀, gp = .send x N gp₀ ∧ S p₀ gp₀
  | .rcfgPrefix x N p₀ => ∃ gp₀, gp = .rcfgPrefix x N gp₀ ∧ S p₀ gp₀
  | .parallel p₁ p₂ => ∃ g₁ g₂, gp = .parallel g₁ g₂ ∧ S p₁ g₁ ∧ S p₂ g₂
  | .choice p₁ p₂ => ∃ g₁ g₂, gp = .choice g₁ g₂ ∧ S p₁ g₁ ∧ S p₂ g₂
  | .leftMerge p₁ p₂ => ∃ g₁ g₂, gp = .leftMerge g₁ g₂ ∧ S p₁ g₁ ∧ S p₂ g₂
  | .commMerge p₁ p₂ => ∃ g₁ g₂, gp = .commMerge g₁ g₂ ∧ S p₁ g₁ ∧ S p₂ g₂
  | .restrict L p₀ => ∃ gp₀, gp = .restrict L gp₀ ∧ S p₀ gp₀
  | .project n p₀ => ∃ gp₀, gp = .project n gp₀ ∧ S p₀ gp₀
  | .var x => ∃ i, gp = .ref i ∧ ∃ b, env.lookup x = some b ∧ S b (G.label i)

/-- The closure condition, destructing on the graph shape: for every pair
    in `S`, the graph shape determines the process shape and the component
    pairs must again lie in `S`. -/
def CorrFArm (G : ProcessGraph schema) (env : RecEnv schema) (S : DyNetKAT schema → GProc schema → Prop)
    (p : DyNetKAT schema) (gp : GProc schema) : Prop :=
  match gp with
  | .deadlock => p = .deadlock
  | .nSeq N gp₀ => ∃ p₀, p = .nSeq N p₀ ∧ S p₀ gp₀
  | .recv x N gp₀ => ∃ p₀, p = .recv x N p₀ ∧ S p₀ gp₀
  | .send x N gp₀ => ∃ p₀, p = .send x N p₀ ∧ S p₀ gp₀
  | .rcfgPrefix x N gp₀ => ∃ p₀, p = .rcfgPrefix x N p₀ ∧ S p₀ gp₀
  | .parallel g₁ g₂ => ∃ p₁ p₂, p = .parallel p₁ p₂ ∧ S p₁ g₁ ∧ S p₂ g₂
  | .choice g₁ g₂ => ∃ p₁ p₂, p = .choice p₁ p₂ ∧ S p₁ g₁ ∧ S p₂ g₂
  | .leftMerge g₁ g₂ => ∃ p₁ p₂, p = .leftMerge p₁ p₂ ∧ S p₁ g₁ ∧ S p₂ g₂
  | .commMerge g₁ g₂ => ∃ p₁ p₂, p = .commMerge p₁ p₂ ∧ S p₁ g₁ ∧ S p₂ g₂
  | .restrict L gp₀ => ∃ p₀, p = .restrict L p₀ ∧ S p₀ gp₀
  | .project n gp₀ => ∃ p₀, p = .project n p₀ ∧ S p₀ gp₀
  | .ref i => ∃ x b, p = .var x ∧ env.lookup x = some b ∧ S b (G.label i)

/-- A relation is correspondence-closed when every pair in it satisfies
    both closure conditions. -/
def IsCorrespondence (G : ProcessGraph schema) (env : RecEnv schema)
    (S : DyNetKAT schema → GProc schema → Prop) : Prop :=
  (∀ p gp, S p gp → CorrBArm G env S p gp) ∧
  (∀ p gp, S p gp → CorrFArm G env S p gp)

/-- The process/graph correspondence: membership in some
    correspondence-closed relation. -/
def Corr (G : ProcessGraph schema) (env : RecEnv schema) (p : DyNetKAT schema) (gp : GProc schema) : Prop :=
  ∃ S : DyNetKAT schema → GProc schema → Prop, IsCorrespondence G env S ∧ S p gp

------------------------------------------------------------------------
-- §4.1 Inversion lemmas
------------------------------------------------------------------------

theorem corr_nSeq_inv {G : ProcessGraph schema} {env : RecEnv schema} {N : NetKAT schema}
    {p gp : _} (h : Corr G env (.nSeq N p) gp) :
    ∃ gp₀, gp = .nSeq N gp₀ ∧ Corr G env p gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨gp₀, heq, hp₀⟩ := hS.1 _ _ hp
  exact ⟨gp₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_recv_inv {G : ProcessGraph schema} {env : RecEnv schema} {x : Channel} {N : NetKAT schema}
    {p gp : _} (h : Corr G env (.recv x N p) gp) :
    ∃ gp₀, gp = .recv x N gp₀ ∧ Corr G env p gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨gp₀, heq, hp₀⟩ := hS.1 _ _ hp
  exact ⟨gp₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_send_inv {G : ProcessGraph schema} {env : RecEnv schema} {x : Channel} {N : NetKAT schema}
    {p gp : _} (h : Corr G env (.send x N p) gp) :
    ∃ gp₀, gp = .send x N gp₀ ∧ Corr G env p gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨gp₀, heq, hp₀⟩ := hS.1 _ _ hp
  exact ⟨gp₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_rcfgPrefix_inv {G : ProcessGraph schema} {env : RecEnv schema} {x : Channel} {N : NetKAT schema}
    {p gp : _} (h : Corr G env (.rcfgPrefix x N p) gp) :
    ∃ gp₀, gp = .rcfgPrefix x N gp₀ ∧ Corr G env p gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨gp₀, heq, hp₀⟩ := hS.1 _ _ hp
  exact ⟨gp₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_parallel_inv {G : ProcessGraph schema} {env : RecEnv schema} {p₁ p₂ gp : _}
    (h : Corr G env (.parallel p₁ p₂) gp) :
    ∃ g₁ g₂, gp = .parallel g₁ g₂ ∧ Corr G env p₁ g₁ ∧ Corr G env p₂ g₂ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨g₁, g₂, heq, hp₁, hp₂⟩ := hS.1 _ _ hp
  exact ⟨g₁, g₂, heq, ⟨S, hS, hp₁⟩, ⟨S, hS, hp₂⟩⟩

theorem corr_choice_inv {G : ProcessGraph schema} {env : RecEnv schema} {p₁ p₂ gp : _}
    (h : Corr G env (.choice p₁ p₂) gp) :
    ∃ g₁ g₂, gp = .choice g₁ g₂ ∧ Corr G env p₁ g₁ ∧ Corr G env p₂ g₂ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨g₁, g₂, heq, hp₁, hp₂⟩ := hS.1 _ _ hp
  exact ⟨g₁, g₂, heq, ⟨S, hS, hp₁⟩, ⟨S, hS, hp₂⟩⟩

theorem corr_leftMerge_inv {G : ProcessGraph schema} {env : RecEnv schema} {p₁ p₂ gp : _}
    (h : Corr G env (.leftMerge p₁ p₂) gp) :
    ∃ g₁ g₂, gp = .leftMerge g₁ g₂ ∧ Corr G env p₁ g₁ ∧ Corr G env p₂ g₂ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨g₁, g₂, heq, hp₁, hp₂⟩ := hS.1 _ _ hp
  exact ⟨g₁, g₂, heq, ⟨S, hS, hp₁⟩, ⟨S, hS, hp₂⟩⟩

theorem corr_commMerge_inv {G : ProcessGraph schema} {env : RecEnv schema} {p₁ p₂ gp : _}
    (h : Corr G env (.commMerge p₁ p₂) gp) :
    ∃ g₁ g₂, gp = .commMerge g₁ g₂ ∧ Corr G env p₁ g₁ ∧ Corr G env p₂ g₂ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨g₁, g₂, heq, hp₁, hp₂⟩ := hS.1 _ _ hp
  exact ⟨g₁, g₂, heq, ⟨S, hS, hp₁⟩, ⟨S, hS, hp₂⟩⟩

theorem corr_restrict_inv {G : ProcessGraph schema} {env : RecEnv schema} {L : Set (CommunicationAction schema)}
    {p gp : _} (h : Corr G env (.restrict L p) gp) :
    ∃ gp₀, gp = .restrict L gp₀ ∧ Corr G env p gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨gp₀, heq, hp₀⟩ := hS.1 _ _ hp
  exact ⟨gp₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_project_inv {G : ProcessGraph schema} {env : RecEnv schema} {n : Nat}
    {p gp : _} (h : Corr G env (.project n p) gp) :
    ∃ gp₀, gp = .project n gp₀ ∧ Corr G env p gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨gp₀, heq, hp₀⟩ := hS.1 _ _ hp
  exact ⟨gp₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_var_inv {G : ProcessGraph schema} {env : RecEnv schema} {x : Var} {gp : _}
    (h : Corr G env (.var x) gp) :
    ∃ i b, gp = .ref i ∧ env.lookup x = some b ∧ Corr G env b (G.label i) := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨i, heq, b, hb, hp₀⟩ := hS.1 _ _ hp
  exact ⟨i, b, heq, hb, ⟨S, hS, hp₀⟩⟩

/-- Inversion on the graph side: a correspondence with an `nSeq` node
    forces the process to have the same prefix. -/
theorem corr_gp_nSeq_inv {G : ProcessGraph schema} {env : RecEnv schema} {N : NetKAT schema}
    {gp₀ : GProc schema} {p : DyNetKAT schema} (h : Corr G env p (.nSeq N gp₀)) :
    ∃ p₀, p = .nSeq N p₀ ∧ Corr G env p₀ gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨p₀, heq, hp₀⟩ := hS.2 _ _ hp
  exact ⟨p₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_gp_recv_inv {G : ProcessGraph schema} {env : RecEnv schema} {x : Channel} {N : NetKAT schema}
    {gp₀ : GProc schema} {p : DyNetKAT schema} (h : Corr G env p (.recv x N gp₀)) :
    ∃ p₀, p = .recv x N p₀ ∧ Corr G env p₀ gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨p₀, heq, hp₀⟩ := hS.2 _ _ hp
  exact ⟨p₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_gp_send_inv {G : ProcessGraph schema} {env : RecEnv schema} {x : Channel} {N : NetKAT schema}
    {gp₀ : GProc schema} {p : DyNetKAT schema} (h : Corr G env p (.send x N gp₀)) :
    ∃ p₀, p = .send x N p₀ ∧ Corr G env p₀ gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨p₀, heq, hp₀⟩ := hS.2 _ _ hp
  exact ⟨p₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_gp_rcfgPrefix_inv {G : ProcessGraph schema} {env : RecEnv schema} {x : Channel}
    {N : NetKAT schema} {gp₀ : GProc schema} {p : DyNetKAT schema} (h : Corr G env p (.rcfgPrefix x N gp₀)) :
    ∃ p₀, p = .rcfgPrefix x N p₀ ∧ Corr G env p₀ gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨p₀, heq, hp₀⟩ := hS.2 _ _ hp
  exact ⟨p₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_gp_parallel_inv {G : ProcessGraph schema} {env : RecEnv schema} {g₁ g₂ : GProc schema}
    {p : DyNetKAT schema} (h : Corr G env p (.parallel g₁ g₂)) :
    ∃ p₁ p₂, p = .parallel p₁ p₂ ∧ Corr G env p₁ g₁ ∧ Corr G env p₂ g₂ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨p₁, p₂, heq, hp₁, hp₂⟩ := hS.2 _ _ hp
  exact ⟨p₁, p₂, heq, ⟨S, hS, hp₁⟩, ⟨S, hS, hp₂⟩⟩

theorem corr_gp_choice_inv {G : ProcessGraph schema} {env : RecEnv schema} {g₁ g₂ : GProc schema}
    {p : DyNetKAT schema} (h : Corr G env p (.choice g₁ g₂)) :
    ∃ p₁ p₂, p = .choice p₁ p₂ ∧ Corr G env p₁ g₁ ∧ Corr G env p₂ g₂ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨p₁, p₂, heq, hp₁, hp₂⟩ := hS.2 _ _ hp
  exact ⟨p₁, p₂, heq, ⟨S, hS, hp₁⟩, ⟨S, hS, hp₂⟩⟩

theorem corr_gp_leftMerge_inv {G : ProcessGraph schema} {env : RecEnv schema} {g₁ g₂ : GProc schema}
    {p : DyNetKAT schema} (h : Corr G env p (.leftMerge g₁ g₂)) :
    ∃ p₁ p₂, p = .leftMerge p₁ p₂ ∧ Corr G env p₁ g₁ ∧ Corr G env p₂ g₂ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨p₁, p₂, heq, hp₁, hp₂⟩ := hS.2 _ _ hp
  exact ⟨p₁, p₂, heq, ⟨S, hS, hp₁⟩, ⟨S, hS, hp₂⟩⟩

theorem corr_gp_commMerge_inv {G : ProcessGraph schema} {env : RecEnv schema} {g₁ g₂ : GProc schema}
    {p : DyNetKAT schema} (h : Corr G env p (.commMerge g₁ g₂)) :
    ∃ p₁ p₂, p = .commMerge p₁ p₂ ∧ Corr G env p₁ g₁ ∧ Corr G env p₂ g₂ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨p₁, p₂, heq, hp₁, hp₂⟩ := hS.2 _ _ hp
  exact ⟨p₁, p₂, heq, ⟨S, hS, hp₁⟩, ⟨S, hS, hp₂⟩⟩

theorem corr_gp_restrict_inv {G : ProcessGraph schema} {env : RecEnv schema}
    {L : Set (CommunicationAction schema)} {gp₀ : GProc schema} {p : DyNetKAT schema}
    (h : Corr G env p (.restrict L gp₀)) :
    ∃ p₀, p = .restrict L p₀ ∧ Corr G env p₀ gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨p₀, heq, hp₀⟩ := hS.2 _ _ hp
  exact ⟨p₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_gp_project_inv {G : ProcessGraph schema} {env : RecEnv schema} {n : Nat}
    {gp₀ : GProc schema} {p : DyNetKAT schema} (h : Corr G env p (.project n gp₀)) :
    ∃ p₀, p = .project n p₀ ∧ Corr G env p₀ gp₀ := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨p₀, heq, hp₀⟩ := hS.2 _ _ hp
  exact ⟨p₀, heq, ⟨S, hS, hp₀⟩⟩

theorem corr_gp_ref_inv {G : ProcessGraph schema} {env : RecEnv schema} {i : NodeId}
    {p : DyNetKAT schema} (h : Corr G env p (.ref i)) :
    ∃ x b, p = .var x ∧ env.lookup x = some b ∧ Corr G env b (G.label i) := by
  obtain ⟨S, hS, hp⟩ := h
  obtain ⟨x, b, heq, hb, hp₀⟩ := hS.2 _ _ hp
  exact ⟨x, b, heq, hb, ⟨S, hS, hp₀⟩⟩

------------------------------------------------------------------------
-- §4.2 Transfer lemmas and introduction lemmas
--
-- The transfer lemmas run the closure condition of one witness through
-- a pointwise inclusion, so every introduction lemma only has to handle
-- its own root pair; the component pairs are delegated to the component
-- witnesses.
------------------------------------------------------------------------

theorem corrB_transfer_at {G : ProcessGraph schema} {env : RecEnv schema}
    {S₁ S₂ : DyNetKAT schema → GProc schema → Prop}
    (hS₁ : ∀ p gp, S₁ p gp → CorrBArm G env S₁ p gp)
    (hle : ∀ a b, S₁ a b → S₂ a b)
    (p : DyNetKAT schema) (gp : GProc schema) (hp : S₁ p gp) :
    CorrBArm G env S₂ p gp := by
  cases p with
  | deadlock => exact hS₁ _ _ hp
  | nSeq N p₀ => obtain ⟨gp₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨gp₀, heq, hle _ _ hc⟩
  | recv x N p₀ => obtain ⟨gp₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨gp₀, heq, hle _ _ hc⟩
  | send x N p₀ => obtain ⟨gp₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨gp₀, heq, hle _ _ hc⟩
  | rcfgPrefix x N p₀ => obtain ⟨gp₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨gp₀, heq, hle _ _ hc⟩
  | parallel p₁ p₂ =>
      obtain ⟨g₁, g₂, heq, hc₁, hc₂⟩ := hS₁ _ _ hp
      exact ⟨g₁, g₂, heq, hle _ _ hc₁, hle _ _ hc₂⟩
  | choice p₁ p₂ =>
      obtain ⟨g₁, g₂, heq, hc₁, hc₂⟩ := hS₁ _ _ hp
      exact ⟨g₁, g₂, heq, hle _ _ hc₁, hle _ _ hc₂⟩
  | leftMerge p₁ p₂ =>
      obtain ⟨g₁, g₂, heq, hc₁, hc₂⟩ := hS₁ _ _ hp
      exact ⟨g₁, g₂, heq, hle _ _ hc₁, hle _ _ hc₂⟩
  | commMerge p₁ p₂ =>
      obtain ⟨g₁, g₂, heq, hc₁, hc₂⟩ := hS₁ _ _ hp
      exact ⟨g₁, g₂, heq, hle _ _ hc₁, hle _ _ hc₂⟩
  | restrict L p₀ => obtain ⟨gp₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨gp₀, heq, hle _ _ hc⟩
  | project n p₀ => obtain ⟨gp₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨gp₀, heq, hle _ _ hc⟩
  | var x =>
      obtain ⟨i, heq, b, hb, hc⟩ := hS₁ _ _ hp
      exact ⟨i, heq, b, hb, hle _ _ hc⟩

theorem corrF_transfer_at {G : ProcessGraph schema} {env : RecEnv schema}
    {S₁ S₂ : DyNetKAT schema → GProc schema → Prop}
    (hS₁ : ∀ p gp, S₁ p gp → CorrFArm G env S₁ p gp)
    (hle : ∀ a b, S₁ a b → S₂ a b)
    (p : DyNetKAT schema) (gp : GProc schema) (hp : S₁ p gp) :
    CorrFArm G env S₂ p gp := by
  cases gp with
  | deadlock => exact hS₁ _ _ hp
  | nSeq N gp₀ => obtain ⟨p₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨p₀, heq, hle _ _ hc⟩
  | recv x N gp₀ => obtain ⟨p₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨p₀, heq, hle _ _ hc⟩
  | send x N gp₀ => obtain ⟨p₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨p₀, heq, hle _ _ hc⟩
  | rcfgPrefix x N gp₀ => obtain ⟨p₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨p₀, heq, hle _ _ hc⟩
  | parallel g₁ g₂ =>
      obtain ⟨p₁, p₂, heq, hc₁, hc₂⟩ := hS₁ _ _ hp
      exact ⟨p₁, p₂, heq, hle _ _ hc₁, hle _ _ hc₂⟩
  | choice g₁ g₂ =>
      obtain ⟨p₁, p₂, heq, hc₁, hc₂⟩ := hS₁ _ _ hp
      exact ⟨p₁, p₂, heq, hle _ _ hc₁, hle _ _ hc₂⟩
  | leftMerge g₁ g₂ =>
      obtain ⟨p₁, p₂, heq, hc₁, hc₂⟩ := hS₁ _ _ hp
      exact ⟨p₁, p₂, heq, hle _ _ hc₁, hle _ _ hc₂⟩
  | commMerge g₁ g₂ =>
      obtain ⟨p₁, p₂, heq, hc₁, hc₂⟩ := hS₁ _ _ hp
      exact ⟨p₁, p₂, heq, hle _ _ hc₁, hle _ _ hc₂⟩
  | restrict L gp₀ => obtain ⟨p₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨p₀, heq, hle _ _ hc⟩
  | project n gp₀ => obtain ⟨p₀, heq, hc⟩ := hS₁ _ _ hp; exact ⟨p₀, heq, hle _ _ hc⟩
  | ref i =>
      obtain ⟨x, b, heq, hb, hc⟩ := hS₁ _ _ hp
      exact ⟨x, b, heq, hb, hle _ _ hc⟩

------------------------------------------------------------------------
-- §4.3 Introduction lemmas
--
-- Each witness is `root pair ∨ S₁ ∨ S₂`: the root pair is discharged
-- directly (its shape is concrete), and every pair coming from `S₁` or
-- `S₂` is delegated through the transfer lemmas.
------------------------------------------------------------------------

theorem corr_deadlock_intro (G : ProcessGraph schema) (env : RecEnv schema) :
    Corr G env .deadlock .deadlock := by
  refine ⟨fun a b => a = .deadlock ∧ b = .deadlock, ⟨?_, ?_⟩, ⟨rfl, rfl⟩⟩
  · intro a b hab
    cases a with
    | deadlock => exact hab.2
    | nSeq N p₀ => exact absurd hab.1 (by simp)
    | recv x N p₀ => exact absurd hab.1 (by simp)
    | send x N p₀ => exact absurd hab.1 (by simp)
    | rcfgPrefix x N p₀ => exact absurd hab.1 (by simp)
    | parallel p₁ p₂ => exact absurd hab.1 (by simp)
    | choice p₁ p₂ => exact absurd hab.1 (by simp)
    | leftMerge p₁ p₂ => exact absurd hab.1 (by simp)
    | commMerge p₁ p₂ => exact absurd hab.1 (by simp)
    | restrict L p₀ => exact absurd hab.1 (by simp)
    | project n p₀ => exact absurd hab.1 (by simp)
    | var x => exact absurd hab.1 (by simp)
  · intro a b hab
    cases b with
    | deadlock => exact hab.1
    | nSeq N gp₀ => exact absurd hab.2 (by simp)
    | recv x N gp₀ => exact absurd hab.2 (by simp)
    | send x N gp₀ => exact absurd hab.2 (by simp)
    | rcfgPrefix x N gp₀ => exact absurd hab.2 (by simp)
    | parallel g₁ g₂ => exact absurd hab.2 (by simp)
    | choice g₁ g₂ => exact absurd hab.2 (by simp)
    | leftMerge g₁ g₂ => exact absurd hab.2 (by simp)
    | commMerge g₁ g₂ => exact absurd hab.2 (by simp)
    | restrict L gp₀ => exact absurd hab.2 (by simp)
    | project n gp₀ => exact absurd hab.2 (by simp)
    | ref i => exact absurd hab.2 (by simp)

theorem corr_var_intro {G : ProcessGraph schema} {env : RecEnv schema} {x : Var} {i : NodeId}
    {b : DyNetKAT schema} (hb : env.lookup x = some b) (hc : Corr G env b (G.label i)) :
    Corr G env (.var x) (.ref i) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := hc
  refine ⟨fun a c => (a = .var x ∧ c = .ref i) ∨ S₁ a c, ⟨?_, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
  · intro a c hab
    rcases hab with ⟨ha, hci⟩ | h
    · subst ha; subst hci
      exact ⟨i, rfl, b, hb, Or.inr hp₁⟩
    · exact corrB_transfer_at hS₁.1 (fun a c h => Or.inr h) a c h
  · intro a c hab
    rcases hab with ⟨ha, hci⟩ | h
    · subst ha; subst hci
      exact ⟨x, b, rfl, hb, Or.inr hp₁⟩
    · exact corrF_transfer_at hS₁.2 (fun a c h => Or.inr h) a c h

theorem corr_nSeq_intro {G : ProcessGraph schema} {env : RecEnv schema} {N : NetKAT schema} {p gp : _}
    (h : Corr G env p gp) :
    Corr G env (.nSeq N p) (.nSeq N gp) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := h
  refine ⟨fun a b => (a = .nSeq N p ∧ b = .nSeq N gp) ∨ S₁ a b, ⟨?_, ?_⟩,
    Or.inl ⟨rfl, rfl⟩⟩
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨gp, rfl, Or.inr hp₁⟩
    · exact corrB_transfer_at hS₁.1 (fun a b h => Or.inr h) a b h
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨p, rfl, Or.inr hp₁⟩
    · exact corrF_transfer_at hS₁.2 (fun a b h => Or.inr h) a b h

theorem corr_recv_intro {G : ProcessGraph schema} {env : RecEnv schema} {x : Channel} {N : NetKAT schema}
    {p gp : _} (h : Corr G env p gp) :
    Corr G env (.recv x N p) (.recv x N gp) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := h
  refine ⟨fun a b => (a = .recv x N p ∧ b = .recv x N gp) ∨ S₁ a b, ⟨?_, ?_⟩,
    Or.inl ⟨rfl, rfl⟩⟩
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨gp, rfl, Or.inr hp₁⟩
    · exact corrB_transfer_at hS₁.1 (fun a b h => Or.inr h) a b h
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨p, rfl, Or.inr hp₁⟩
    · exact corrF_transfer_at hS₁.2 (fun a b h => Or.inr h) a b h

theorem corr_send_intro {G : ProcessGraph schema} {env : RecEnv schema} {x : Channel} {N : NetKAT schema}
    {p gp : _} (h : Corr G env p gp) :
    Corr G env (.send x N p) (.send x N gp) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := h
  refine ⟨fun a b => (a = .send x N p ∧ b = .send x N gp) ∨ S₁ a b, ⟨?_, ?_⟩,
    Or.inl ⟨rfl, rfl⟩⟩
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨gp, rfl, Or.inr hp₁⟩
    · exact corrB_transfer_at hS₁.1 (fun a b h => Or.inr h) a b h
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨p, rfl, Or.inr hp₁⟩
    · exact corrF_transfer_at hS₁.2 (fun a b h => Or.inr h) a b h

theorem corr_rcfgPrefix_intro {G : ProcessGraph schema} {env : RecEnv schema} {x : Channel}
    {N : NetKAT schema} {p gp : _} (h : Corr G env p gp) :
    Corr G env (.rcfgPrefix x N p) (.rcfgPrefix x N gp) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := h
  refine ⟨fun a b => (a = .rcfgPrefix x N p ∧ b = .rcfgPrefix x N gp) ∨ S₁ a b,
    ⟨?_, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨gp, rfl, Or.inr hp₁⟩
    · exact corrB_transfer_at hS₁.1 (fun a b h => Or.inr h) a b h
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨p, rfl, Or.inr hp₁⟩
    · exact corrF_transfer_at hS₁.2 (fun a b h => Or.inr h) a b h

theorem corr_parallel_intro {G : ProcessGraph schema} {env : RecEnv schema} {p₁ p₂ g₁ g₂ : _}
    (h₁ : Corr G env p₁ g₁) (h₂ : Corr G env p₂ g₂) :
    Corr G env (.parallel p₁ p₂) (.parallel g₁ g₂) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := h₁
  obtain ⟨S₂, hS₂, hp₂⟩ := h₂
  refine ⟨fun a b => (a = .parallel p₁ p₂ ∧ b = .parallel g₁ g₂) ∨ S₁ a b ∨ S₂ a b,
    ⟨?_, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h | h
    · subst ha; subst hb
      exact ⟨g₁, g₂, rfl, Or.inr (Or.inl hp₁), Or.inr (Or.inr hp₂)⟩
    · exact corrB_transfer_at hS₁.1 (fun a b h => Or.inr (Or.inl h)) a b h
    · exact corrB_transfer_at hS₂.1 (fun a b h => Or.inr (Or.inr h)) a b h
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h | h
    · subst ha; subst hb
      exact ⟨p₁, p₂, rfl, Or.inr (Or.inl hp₁), Or.inr (Or.inr hp₂)⟩
    · exact corrF_transfer_at hS₁.2 (fun a b h => Or.inr (Or.inl h)) a b h
    · exact corrF_transfer_at hS₂.2 (fun a b h => Or.inr (Or.inr h)) a b h

theorem corr_choice_intro {G : ProcessGraph schema} {env : RecEnv schema} {p₁ p₂ g₁ g₂ : _}
    (h₁ : Corr G env p₁ g₁) (h₂ : Corr G env p₂ g₂) :
    Corr G env (.choice p₁ p₂) (.choice g₁ g₂) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := h₁
  obtain ⟨S₂, hS₂, hp₂⟩ := h₂
  refine ⟨fun a b => (a = .choice p₁ p₂ ∧ b = .choice g₁ g₂) ∨ S₁ a b ∨ S₂ a b,
    ⟨?_, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h | h
    · subst ha; subst hb
      exact ⟨g₁, g₂, rfl, Or.inr (Or.inl hp₁), Or.inr (Or.inr hp₂)⟩
    · exact corrB_transfer_at hS₁.1 (fun a b h => Or.inr (Or.inl h)) a b h
    · exact corrB_transfer_at hS₂.1 (fun a b h => Or.inr (Or.inr h)) a b h
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h | h
    · subst ha; subst hb
      exact ⟨p₁, p₂, rfl, Or.inr (Or.inl hp₁), Or.inr (Or.inr hp₂)⟩
    · exact corrF_transfer_at hS₁.2 (fun a b h => Or.inr (Or.inl h)) a b h
    · exact corrF_transfer_at hS₂.2 (fun a b h => Or.inr (Or.inr h)) a b h

theorem corr_leftMerge_intro {G : ProcessGraph schema} {env : RecEnv schema} {p₁ p₂ g₁ g₂ : _}
    (h₁ : Corr G env p₁ g₁) (h₂ : Corr G env p₂ g₂) :
    Corr G env (.leftMerge p₁ p₂) (.leftMerge g₁ g₂) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := h₁
  obtain ⟨S₂, hS₂, hp₂⟩ := h₂
  refine ⟨fun a b => (a = .leftMerge p₁ p₂ ∧ b = .leftMerge g₁ g₂) ∨ S₁ a b ∨ S₂ a b,
    ⟨?_, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h | h
    · subst ha; subst hb
      exact ⟨g₁, g₂, rfl, Or.inr (Or.inl hp₁), Or.inr (Or.inr hp₂)⟩
    · exact corrB_transfer_at hS₁.1 (fun a b h => Or.inr (Or.inl h)) a b h
    · exact corrB_transfer_at hS₂.1 (fun a b h => Or.inr (Or.inr h)) a b h
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h | h
    · subst ha; subst hb
      exact ⟨p₁, p₂, rfl, Or.inr (Or.inl hp₁), Or.inr (Or.inr hp₂)⟩
    · exact corrF_transfer_at hS₁.2 (fun a b h => Or.inr (Or.inl h)) a b h
    · exact corrF_transfer_at hS₂.2 (fun a b h => Or.inr (Or.inr h)) a b h

theorem corr_commMerge_intro {G : ProcessGraph schema} {env : RecEnv schema} {p₁ p₂ g₁ g₂ : _}
    (h₁ : Corr G env p₁ g₁) (h₂ : Corr G env p₂ g₂) :
    Corr G env (.commMerge p₁ p₂) (.commMerge g₁ g₂) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := h₁
  obtain ⟨S₂, hS₂, hp₂⟩ := h₂
  refine ⟨fun a b => (a = .commMerge p₁ p₂ ∧ b = .commMerge g₁ g₂) ∨ S₁ a b ∨ S₂ a b,
    ⟨?_, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h | h
    · subst ha; subst hb
      exact ⟨g₁, g₂, rfl, Or.inr (Or.inl hp₁), Or.inr (Or.inr hp₂)⟩
    · exact corrB_transfer_at hS₁.1 (fun a b h => Or.inr (Or.inl h)) a b h
    · exact corrB_transfer_at hS₂.1 (fun a b h => Or.inr (Or.inr h)) a b h
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h | h
    · subst ha; subst hb
      exact ⟨p₁, p₂, rfl, Or.inr (Or.inl hp₁), Or.inr (Or.inr hp₂)⟩
    · exact corrF_transfer_at hS₁.2 (fun a b h => Or.inr (Or.inl h)) a b h
    · exact corrF_transfer_at hS₂.2 (fun a b h => Or.inr (Or.inr h)) a b h

theorem corr_restrict_intro {G : ProcessGraph schema} {env : RecEnv schema}
    {L : Set (CommunicationAction schema)} {p gp : _} (h : Corr G env p gp) :
    Corr G env (.restrict L p) (.restrict L gp) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := h
  refine ⟨fun a b => (a = .restrict L p ∧ b = .restrict L gp) ∨ S₁ a b, ⟨?_, ?_⟩,
    Or.inl ⟨rfl, rfl⟩⟩
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨gp, rfl, Or.inr hp₁⟩
    · exact corrB_transfer_at hS₁.1 (fun a b h => Or.inr h) a b h
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨p, rfl, Or.inr hp₁⟩
    · exact corrF_transfer_at hS₁.2 (fun a b h => Or.inr h) a b h

theorem corr_project_intro {G : ProcessGraph schema} {env : RecEnv schema} {n : Nat} {p gp : _}
    (h : Corr G env p gp) :
    Corr G env (.project n p) (.project n gp) := by
  obtain ⟨S₁, hS₁, hp₁⟩ := h
  refine ⟨fun a b => (a = .project n p ∧ b = .project n gp) ∨ S₁ a b, ⟨?_, ?_⟩,
    Or.inl ⟨rfl, rfl⟩⟩
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨gp, rfl, Or.inr hp₁⟩
    · exact corrB_transfer_at hS₁.1 (fun a b h => Or.inr h) a b h
  · intro a b hab
    rcases hab with ⟨ha, hb⟩ | h
    · subst ha; subst hb
      exact ⟨p, rfl, Or.inr hp₁⟩
    · exact corrF_transfer_at hS₁.2 (fun a b h => Or.inr h) a b h

------------------------------------------------------------------------
-- §5 Soundness and completeness of the graph semantics
------------------------------------------------------------------------

/-- **Graph soundness**: every graph transition of a node corresponds to a
    valid transition of the corresponding process in the environment-indexed
    SOS, and the destination process corresponds to the destination node. -/
theorem gstep_to_step (G : ProcessGraph schema) (env : RecEnv schema) (gc gc' : GConfig schema) (a : Action schema)
    (hstep : GStep G gc a gc') :
    ∀ (p : DyNetKAT schema), Corr G env p gc.proc →
      ∃ (p' : DyNetKAT schema),
        Step env
          (show (Config schema) from
            { proc := p, pending := gc.pending, handled := gc.handled }) a
          (show (Config schema) from
            { proc := p', pending := gc'.pending, handled := gc'.handled }) ∧
        Corr G env p' gc'.proc := by
  induction hstep with
  | seq_ok N cont σ σ' pt₀ hl₀ evaluates =>
      intro p hcorr
      obtain ⟨p₀, rfl, hp₀⟩ := corr_gp_nSeq_inv hcorr
      exact ⟨p₀, Step.cpol_seq_ok N p₀ σ σ' pt₀ hl₀ evaluates, hp₀⟩
  | choice_l gp gq gp' a pt₀ pt' hl₀ hl' steps ih =>
      intro p hcorr
      obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := corr_gp_choice_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih p₁ hp₁
      exact ⟨q, Step.cpol_choice_l p₁ p₂ q a pt₀ pt' hl₀ hl' hq, hcq⟩
  | choice_r gp gq gq' a pt₀ pt' hl₀ hl' steps ih =>
      intro p hcorr
      obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := corr_gp_choice_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih p₂ hp₂
      exact ⟨q, Step.cpol_choice_r p₁ p₂ q a pt₀ pt' hl₀ hl' hq, hcq⟩
  | par_l gp gq gp' a pt₀ pt' hl₀ hl' steps ih =>
      intro p hcorr
      obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := corr_gp_parallel_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih p₁ hp₁
      exact ⟨.parallel q p₂,
        Step.cpol_par_l p₁ p₂ q a pt₀ pt' hl₀ hl' hq,
        corr_parallel_intro hcq hp₂⟩
  | par_r gp gq gq' a pt₀ pt' hl₀ hl' steps ih =>
      intro p hcorr
      obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := corr_gp_parallel_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih p₂ hp₂
      exact ⟨.parallel p₁ q,
        Step.cpol_par_r p₁ p₂ q a pt₀ pt' hl₀ hl' hq,
        corr_parallel_intro hp₁ hcq⟩
  | left_merge gp gq gp' a pt₀ pt' hl₀ hl' steps ih =>
      intro p hcorr
      obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := corr_gp_leftMerge_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih p₁ hp₁
      exact ⟨.parallel q p₂,
        Step.cpol_left_merge p₁ p₂ q a pt₀ pt' hl₀ hl' hq,
        corr_parallel_intro hcq hp₂⟩
  | comm_merge_recv_send x r gp gs gp' gs' pt₀ hl₀ recv_step send_step ih_r ih_s =>
      intro p hcorr
      obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := corr_gp_commMerge_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih_r p₁ hp₁
      obtain ⟨s, hs, hcs⟩ := ih_s p₂ hp₂
      exact ⟨.parallel q s,
        Step.cpol_comm_merge_recv_send x r p₁ p₂ q s pt₀ hl₀ hq hs,
        corr_parallel_intro hcq hcs⟩
  | comm_merge_send_recv x r gp gs gp' gs' pt₀ hl₀ send_step recv_step ih_s ih_r =>
      intro p hcorr
      obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := corr_gp_commMerge_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih_s p₁ hp₁
      obtain ⟨s, hs, hcs⟩ := ih_r p₂ hp₂
      exact ⟨.parallel q s,
        Step.cpol_comm_merge_send_recv x r p₁ p₂ q s pt₀ hl₀ hq hs,
        corr_parallel_intro hcq hcs⟩
  | recv x N cont pt₀ hl₀ =>
      intro p hcorr
      obtain ⟨p₀, rfl, hp₀⟩ := corr_gp_recv_inv hcorr
      exact ⟨p₀, Step.cpol_recv x N p₀ pt₀ hl₀, hp₀⟩
  | send x N cont pt₀ hl₀ =>
      intro p hcorr
      obtain ⟨p₀, rfl, hp₀⟩ := corr_gp_send_inv hcorr
      exact ⟨p₀, Step.cpol_send x N p₀ pt₀ hl₀, hp₀⟩
  | rcfg x N cont pt₀ hl₀ =>
      intro p hcorr
      obtain ⟨p₀, rfl, hp₀⟩ := corr_gp_rcfgPrefix_inv hcorr
      exact ⟨p₀, Step.cpol_rcfg x N p₀ pt₀ hl₀, hp₀⟩
  | var i gp' a pt₀ pt' hl₀ hl' step ih =>
      intro p hcorr
      obtain ⟨x, b, rfl, hb, hp₀⟩ := corr_gp_ref_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih b hp₀
      exact ⟨q, Step.cpol_var x b q a pt₀ pt' hl₀ hl' hb hq, hcq⟩
  | sync_recv_send x r gp gs gp' gs' pt₀ hl₀ recv_step send_step ih_r ih_s =>
      intro p hcorr
      obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := corr_gp_parallel_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih_r p₁ hp₁
      obtain ⟨s, hs, hcs⟩ := ih_s p₂ hp₂
      exact ⟨.parallel q s,
        Step.cpol_sync_recv_send x r p₁ p₂ q s pt₀ hl₀ hq hs,
        corr_parallel_intro hcq hcs⟩
  | sync_send_recv x r gp gs gp' gs' pt₀ hl₀ send_step recv_step ih_s ih_r =>
      intro p hcorr
      obtain ⟨p₁, p₂, rfl, hp₁, hp₂⟩ := corr_gp_parallel_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih_s p₁ hp₁
      obtain ⟨s, hs, hcs⟩ := ih_r p₂ hp₂
      exact ⟨.parallel q s,
        Step.cpol_sync_send_recv x r p₁ p₂ q s pt₀ hl₀ hq hs,
        corr_parallel_intro hcq hcs⟩
  | project n gp gp' a pt₀ pt' hl₀ hl' step ih =>
      intro p hcorr
      obtain ⟨p₀, rfl, hp₀⟩ := corr_gp_project_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih p₀ hp₀
      exact ⟨.project n q, Step.cpol_project n p₀ q a pt₀ pt' hl₀ hl' hq,
        corr_project_intro hcq⟩
  | restrict L gp gp' a pt₀ pt' hl₀ hl' allowed step ih =>
      intro p hcorr
      obtain ⟨p₀, rfl, hp₀⟩ := corr_gp_restrict_inv hcorr
      obtain ⟨q, hq, hcq⟩ := ih p₀ hp₀
      exact ⟨.restrict L q,
        Step.cpol_restrict L p₀ q a pt₀ pt' hl₀ hl' allowed hq,
        corr_restrict_intro hcq⟩

/-- **Graph completeness**: every SOS transition of a process corresponds
    to a graph transition of the corresponding node, with the destination
    process corresponding to the destination node. -/
theorem step_to_gstep (G : ProcessGraph schema) (env : RecEnv schema) (c c' : Config schema) (a : Action schema)
    (hstep : Step env c a c') :
    ∀ (gp : GProc schema), Corr G env c.proc gp →
      ∃ (gp' : GProc schema),
        GStep G
          (show (GConfig schema) from
            { proc := gp, pending := c.pending, handled := c.handled }) a
          (show (GConfig schema) from
            { proc := gp', pending := c'.pending, handled := c'.handled }) ∧
        Corr G env c'.proc gp' := by
  induction hstep with
  | cpol_seq_ok N q σ σ' pendingTail handled evaluates =>
      intro gp hcorr
      obtain ⟨gq, rfl, hgq⟩ := corr_nSeq_inv hcorr
      exact ⟨gq, GStep.seq_ok N gq σ σ' pendingTail handled evaluates, hgq⟩
  | cpol_choice_l p₁ p₂ q a pt₀ pt' hl₀ hl' steps ih =>
      intro gp hcorr
      obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := corr_choice_inv hcorr
      obtain ⟨gq, hstep, hcq⟩ := ih g₁ hg₁
      exact ⟨gq, GStep.choice_l g₁ g₂ gq a pt₀ pt' hl₀ hl' hstep, hcq⟩
  | cpol_choice_r p₁ p₂ q a pt₀ pt' hl₀ hl' steps ih =>
      intro gp hcorr
      obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := corr_choice_inv hcorr
      obtain ⟨gq, hstep, hcq⟩ := ih g₂ hg₂
      exact ⟨gq, GStep.choice_r g₁ g₂ gq a pt₀ pt' hl₀ hl' hstep, hcq⟩
  | cpol_par_l p₁ p₂ q a pt₀ pt' hl₀ hl' steps ih =>
      intro gp hcorr
      obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := corr_parallel_inv hcorr
      obtain ⟨gq, hstep, hcq⟩ := ih g₁ hg₁
      exact ⟨.parallel gq g₂,
        GStep.par_l g₁ g₂ gq a pt₀ pt' hl₀ hl' hstep,
        corr_parallel_intro hcq hg₂⟩
  | cpol_par_r p₁ p₂ q a pt₀ pt' hl₀ hl' steps ih =>
      intro gp hcorr
      obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := corr_parallel_inv hcorr
      obtain ⟨gq, hstep, hcq⟩ := ih g₂ hg₂
      exact ⟨.parallel g₁ gq,
        GStep.par_r g₁ g₂ gq a pt₀ pt' hl₀ hl' hstep,
        corr_parallel_intro hg₁ hcq⟩
  | cpol_left_merge p₁ p₂ q a pt₀ pt' hl₀ hl' steps ih =>
      intro gp hcorr
      obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := corr_leftMerge_inv hcorr
      obtain ⟨gq, hstep, hcq⟩ := ih g₁ hg₁
      exact ⟨.parallel gq g₂,
        GStep.left_merge g₁ g₂ gq a pt₀ pt' hl₀ hl' hstep,
        corr_parallel_intro hcq hg₂⟩
  | cpol_comm_merge_recv_send x r q s q' s' pt₀ hl₀ recv_step send_step ih_r ih_s =>
      intro gp hcorr
      obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := corr_commMerge_inv hcorr
      obtain ⟨gq, hstep1, hcq⟩ := ih_r g₁ hg₁
      obtain ⟨gs, hstep2, hcs⟩ := ih_s g₂ hg₂
      exact ⟨.parallel gq gs,
        GStep.comm_merge_recv_send x r g₁ g₂ gq gs pt₀ hl₀ hstep1 hstep2,
        corr_parallel_intro hcq hcs⟩
  | cpol_comm_merge_send_recv x r q s q' s' pt₀ hl₀ send_step recv_step ih_s ih_r =>
      intro gp hcorr
      obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := corr_commMerge_inv hcorr
      obtain ⟨gq, hstep1, hcq⟩ := ih_s g₁ hg₁
      obtain ⟨gs, hstep2, hcs⟩ := ih_r g₂ hg₂
      exact ⟨.parallel gq gs,
        GStep.comm_merge_send_recv x r g₁ g₂ gq gs pt₀ hl₀ hstep1 hstep2,
        corr_parallel_intro hcq hcs⟩
  | cpol_recv x N cont pt₀ hl₀ =>
      intro gp hcorr
      obtain ⟨gc, rfl, hgc⟩ := corr_recv_inv hcorr
      exact ⟨gc, GStep.recv x N gc pt₀ hl₀, hgc⟩
  | cpol_send x N cont pt₀ hl₀ =>
      intro gp hcorr
      obtain ⟨gc, rfl, hgc⟩ := corr_send_inv hcorr
      exact ⟨gc, GStep.send x N gc pt₀ hl₀, hgc⟩
  | cpol_rcfg x N cont pt₀ hl₀ =>
      intro gp hcorr
      obtain ⟨gc, rfl, hgc⟩ := corr_rcfgPrefix_inv hcorr
      exact ⟨gc, GStep.rcfg x N gc pt₀ hl₀, hgc⟩
  | cpol_var name body body' a pt₀ pt' hl₀ hl' definition step ih =>
      intro gp hcorr
      obtain ⟨i, b, rfl, hb, hgp⟩ := corr_var_inv hcorr
      have hbody : body = b := Option.some.inj (definition.symm.trans hb)
      subst hbody
      obtain ⟨gq, hstep, hcq⟩ := ih (G.label i) hgp
      exact ⟨gq, GStep.var i gq a pt₀ pt' hl₀ hl' hstep, hcq⟩
  | cpol_sync_recv_send x r q s q' s' pt₀ hl₀ recv_step send_step ih_r ih_s =>
      intro gp hcorr
      obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := corr_parallel_inv hcorr
      obtain ⟨gq, hstep1, hcq⟩ := ih_r g₁ hg₁
      obtain ⟨gs, hstep2, hcs⟩ := ih_s g₂ hg₂
      exact ⟨.parallel gq gs,
        GStep.sync_recv_send x r g₁ g₂ gq gs pt₀ hl₀ hstep1 hstep2,
        corr_parallel_intro hcq hcs⟩
  | cpol_sync_send_recv x r q s q' s' pt₀ hl₀ send_step recv_step ih_s ih_r =>
      intro gp hcorr
      obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := corr_parallel_inv hcorr
      obtain ⟨gq, hstep1, hcq⟩ := ih_s g₁ hg₁
      obtain ⟨gs, hstep2, hcs⟩ := ih_r g₂ hg₂
      exact ⟨.parallel gq gs,
        GStep.sync_send_recv x r g₁ g₂ gq gs pt₀ hl₀ hstep1 hstep2,
        corr_parallel_intro hcq hcs⟩
  | cpol_project n p₀ q a pt₀ pt' hl₀ hl' step ih =>
      intro gp hcorr
      obtain ⟨g₀, rfl, hg₀⟩ := corr_project_inv hcorr
      obtain ⟨gq, hstep, hcq⟩ := ih g₀ hg₀
      exact ⟨.project n gq, GStep.project n g₀ gq a pt₀ pt' hl₀ hl' hstep,
        corr_project_intro hcq⟩
  | cpol_restrict L p₀ q a pt₀ pt' hl₀ hl' allowed step ih =>
      intro gp hcorr
      obtain ⟨g₀, rfl, hg₀⟩ := corr_restrict_inv hcorr
      obtain ⟨gq, hstep, hcq⟩ := ih g₀ hg₀
      exact ⟨.restrict L gq,
        GStep.restrict L g₀ gq a pt₀ pt' hl₀ hl' allowed hstep,
        corr_restrict_intro hcq⟩

/-- **Combined correspondence** (the central acceptance criterion): for
    corresponding configurations, graph transitions and SOS transitions
    coincide up to the destination correspondence. -/
theorem graph_step_iff (G : ProcessGraph schema) (env : RecEnv schema) (p : DyNetKAT schema) (gp : GProc schema)
    (pt hl : List schema.Packet) (a : Action schema) (hcorr : Corr G env p gp) :
    (∃ (gp' : GProc schema) (pt' hl' : List schema.Packet),
        GStep G
          (show (GConfig schema) from { proc := gp, pending := pt, handled := hl }) a
          (show (GConfig schema) from
            { proc := gp', pending := pt', handled := hl' }) ∧
        ∃ (p' : DyNetKAT schema), Corr G env p' gp') ↔
      ∃ (p' : DyNetKAT schema) (pt' hl' : List schema.Packet),
        Step env
          (show (Config schema) from { proc := p, pending := pt, handled := hl }) a
          (show (Config schema) from
            { proc := p', pending := pt', handled := hl' }) := by
  constructor
  · rintro ⟨gp', pt', hl', hstep, p', hcorr'⟩
    obtain ⟨p'', hstep', _⟩ :=
      gstep_to_step G env
        (show (GConfig schema) from { proc := gp, pending := pt, handled := hl })
        (show (GConfig schema) from { proc := gp', pending := pt', handled := hl' })
        a hstep p hcorr
    exact ⟨p'', pt', hl', hstep'⟩
  · rintro ⟨p', pt', hl', hstep⟩
    obtain ⟨gp', hstep', hc'⟩ :=
      step_to_gstep G env
        (show (Config schema) from { proc := p, pending := pt, handled := hl })
        (show (Config schema) from { proc := p', pending := pt', handled := hl' })
        a hstep gp hcorr
    exact ⟨gp', pt', hl', hstep', p', hc'⟩

------------------------------------------------------------------------
-- §6 Graph construction from an environment (finite support)
--
-- `RecEnv := Var → Option DyNetKAT` places no finiteness restriction: an
-- environment may define infinitely many reachable variables (see
-- `infEnv_no_finite_support` below), so allocating a node for each
-- reachable variable requires an explicit
-- finite-support witness: a finite set `S` of variables containing the
-- direct variables of the root and closed under the bodies of its
-- members.  Under this hypothesis every reachable variable is defined
-- (`reachableVars_subset_of_finiteSupport`) and the construction below
-- is total and constructive — no choice principles are used.
------------------------------------------------------------------------

/-- Finite-support witness: a finite set `S` of variables containing the
    direct variables of `root`, such that every variable in `S` is defined
    and its body only references variables in `S`. -/
def FiniteSupport (env : RecEnv schema) (root : DyNetKAT schema) (S : Finset Var) : Prop :=
  recursiveVars root ⊆ S ∧
    ∀ x ∈ S, ∃ b, env.lookup x = some b ∧ recursiveVars b ⊆ S

/-- Every recursively reachable variable of a finitely supported process
    lies in the support set. -/
theorem reachableVars_subset_of_finiteSupport (env : RecEnv schema) (root : DyNetKAT schema)
    (S : Finset Var) (hsup : FiniteSupport env root S) :
    ∀ name, ReachableVar env root name → name ∈ S := by
  intro name h
  induction h with
  | direct occurs => exact hsup.1 occurs
  | throughDefinition _ definition occurs ih =>
      obtain ⟨b, hb, hbsub⟩ := hsup.2 _ ih
      have hbody : _ = b := Option.some.inj (definition.symm.trans hb)
      subst hbody
      exact hbsub occurs

/-- Translation of a DyNetKAT term into a graph term: recursive variables
    become edges to their canonical nodes; every other constructor is
    carried over verbatim. -/
def toGProc : DyNetKAT schema → GProc schema
  | .deadlock => .deadlock
  | .nSeq N d => .nSeq N (toGProc d)
  | .recv x N d => .recv x N (toGProc d)
  | .send x N d => .send x N (toGProc d)
  | .rcfgPrefix x N d => .rcfgPrefix x N (toGProc d)
  | .parallel a b => .parallel (toGProc a) (toGProc b)
  | .choice a b => .choice (toGProc a) (toGProc b)
  | .leftMerge a b => .leftMerge (toGProc a) (toGProc b)
  | .commMerge a b => .commMerge (toGProc a) (toGProc b)
  | .restrict L d => .restrict L (toGProc d)
  | .project n d => .project n (toGProc d)
  | .var x => .ref (varNode x)

/-- The node references of a translated term are exactly the canonical
    nodes of the directly occurring variables. -/
theorem gprocRefs_toGProc (d : DyNetKAT schema) :
    gprocRefs (toGProc d) = (recursiveVars d).image varNode := by
  induction d with
  | deadlock => simp [toGProc, gprocRefs, recursiveVars]
  | nSeq N d ih => simp [toGProc, gprocRefs, recursiveVars, ih]
  | recv x N d ih => simp [toGProc, gprocRefs, recursiveVars, ih]
  | send x N d ih => simp [toGProc, gprocRefs, recursiveVars, ih]
  | rcfgPrefix x N d ih => simp [toGProc, gprocRefs, recursiveVars, ih]
  | parallel a b iha ihb =>
      simp [toGProc, gprocRefs, recursiveVars, iha, ihb, Finset.image_union]
  | choice a b iha ihb =>
      simp [toGProc, gprocRefs, recursiveVars, iha, ihb, Finset.image_union]
  | leftMerge a b iha ihb =>
      simp [toGProc, gprocRefs, recursiveVars, iha, ihb, Finset.image_union]
  | commMerge a b iha ihb =>
      simp [toGProc, gprocRefs, recursiveVars, iha, ihb, Finset.image_union]
  | restrict L d ih => simp [toGProc, gprocRefs, recursiveVars, ih]
  | project n d ih => simp [toGProc, gprocRefs, recursiveVars, ih]
  | var x => simp [toGProc, gprocRefs, recursiveVars, varNode, Finset.image_singleton]

/-- Materialize the labels before handing the graph to the verifier. -/
private def graphLabels (env : RecEnv schema) (S : Finset Var) : List (Var × (GProc schema)) :=
  (S.sort (· ≤ ·)).map fun x => (x, toGProc ((env.lookup x).getD .deadlock))

private def lookupGraphLabel (labels : List (Var × (GProc schema))) : NodeId → GProc schema
  | Sum.inl x => (labels.lookup x).getD .deadlock
  | Sum.inr _ => .deadlock

/-- Lookup in the compiled table. Identifiers outside its domain are inert. -/
def toGraphLabel (env : RecEnv schema) (S : Finset Var) : NodeId → GProc schema :=
  lookupGraphLabel (graphLabels env S)

@[simp] theorem toGraphLabel_varNode {env : RecEnv schema} {S : Finset Var} {x : Var}
    (hx : x ∈ S) :
    toGraphLabel env S (varNode x) = toGProc ((env.lookup x).getD .deadlock) := by
  have lookup (xs : List Var) (h : x ∈ xs) :
      (xs.map (fun y => (y, toGProc ((env.lookup y).getD .deadlock)))).lookup x =
        some (toGProc ((env.lookup x).getD .deadlock)) := by
    induction xs with
    | nil => simp at h
    | cons y ys ih =>
        by_cases he : x = y
        · subst y
          simp [List.lookup]
        · have hne : (x == y) = false := beq_eq_false_iff_ne.mpr he
          simpa [List.lookup, hne] using ih ((List.mem_cons.mp h).resolve_left he)
  change ((graphLabels env S).lookup x).getD .deadlock = _
  rw [graphLabels, lookup (S.sort (· ≤ ·)) (by simpa using hx)]
  rfl

/-- Construction of the finite recursive process graph from an environment
    under the finite-support hypothesis: one node per supported variable
    (the canonical `varNode x`), the root being the translation of the
    original process.  Fully constructive. -/
def toGraph (env : RecEnv schema) (root : DyNetKAT schema) (S : Finset Var)
    (hsup : FiniteSupport env root S) : ProcessGraph schema :=
  let labels := graphLabels env S
  { nodes := S.image varNode
    root := toGProc root
    label := lookupGraphLabel labels
    root_closed := by
      rw [gprocRefs_toGProc]
      exact Finset.image_subset_image hsup.1
    closed := by
      intro i hi
      cases i with
      | inl x =>
          rw [Finset.mem_image] at hi
          obtain ⟨y, hy, hy_eq⟩ := hi
          have hxy : x = y := by simpa [varNode] using hy_eq.symm
          subst hxy
          obtain ⟨b, hb, hbsub⟩ := hsup.2 x hy
          change gprocRefs (toGraphLabel env S (varNode x)) ⊆ _
          rw [toGraphLabel_varNode hy, hb, Option.getD_some, gprocRefs_toGProc]
          exact Finset.image_subset_image hbsub
      | inr k =>
          rw [Finset.mem_image] at hi
          obtain ⟨y, _, hy_eq⟩ := hi
          simp [varNode] at hy_eq }

@[simp] theorem toGraph_label_varNode {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hsup : FiniteSupport env root S) {x : Var} (hx : x ∈ S) :
    (toGraph env root S hsup).label (varNode x) =
      toGProc ((env.lookup x).getD .deadlock) :=
  toGraphLabel_varNode hx

instance (env : RecEnv schema) (root : DyNetKAT schema) (S : Finset Var) :
    Decidable (FiniteSupport env root S) := by
  have check (x : Var) : Decidable (∃ b, env.lookup x = some b ∧ recursiveVars b ⊆ S) := by
    cases h : env.lookup x with
    | none => simp [h]; infer_instance
    | some b => simp [h]; infer_instance
  letI (x : Var) := check x
  unfold FiniteSupport
  infer_instance

/-- Compile against a supplied finite set of variables. An undefined variable
    or a reference outside the supplied set makes compilation fail. -/
def compileGraph (env : RecEnv schema) (root : DyNetKAT schema) (S : Finset Var) : Option (ProcessGraph schema) :=
  if h : FiniteSupport env root S then some (toGraph env root S h) else none

theorem compileGraph_eq_some_iff {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    {G : ProcessGraph schema} :
    compileGraph env root S = some G ↔
      ∃ h : FiniteSupport env root S, G = toGraph env root S h := by
  unfold compileGraph
  split <;> simp_all [eq_comm]

theorem compileGraph_eq_none_iff (env : RecEnv schema) (root : DyNetKAT schema) (S : Finset Var) :
    compileGraph env root S = none ↔ ¬ FiniteSupport env root S := by
  unfold compileGraph
  split <;> simp_all

/-- The same compiled table interprets every process closed over its support. -/
theorem toGraph_corr_of_subset (env : RecEnv schema) (root : DyNetKAT schema) (S : Finset Var)
    (hsup : FiniteSupport env root S) (p : DyNetKAT schema) (hp : recursiveVars p ⊆ S) :
    Corr (toGraph env root S hsup) env p (toGProc p) := by
  refine ⟨fun p gp => gp = toGProc p ∧ recursiveVars p ⊆ S, ⟨?_, ?_⟩, ⟨rfl, hp⟩⟩
  · intro p gp hp
    obtain ⟨rfl, hsub⟩ := hp
    cases p with
    | deadlock => exact rfl
    | nSeq N d => exact ⟨toGProc d, rfl, ⟨rfl, hsub⟩⟩
    | recv x N d => exact ⟨toGProc d, rfl, ⟨rfl, hsub⟩⟩
    | send x N d => exact ⟨toGProc d, rfl, ⟨rfl, hsub⟩⟩
    | rcfgPrefix x N d => exact ⟨toGProc d, rfl, ⟨rfl, hsub⟩⟩
    | parallel a b =>
        have ha : recursiveVars a ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_left _ hz)
        have hb : recursiveVars b ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_right _ hz)
        exact ⟨toGProc a, toGProc b, rfl, ⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    | choice a b =>
        have ha : recursiveVars a ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_left _ hz)
        have hb : recursiveVars b ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_right _ hz)
        exact ⟨toGProc a, toGProc b, rfl, ⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    | leftMerge a b =>
        have ha : recursiveVars a ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_left _ hz)
        have hb : recursiveVars b ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_right _ hz)
        exact ⟨toGProc a, toGProc b, rfl, ⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    | commMerge a b =>
        have ha : recursiveVars a ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_left _ hz)
        have hb : recursiveVars b ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_right _ hz)
        exact ⟨toGProc a, toGProc b, rfl, ⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    | restrict L d => exact ⟨toGProc d, rfl, ⟨rfl, hsub⟩⟩
    | project n d => exact ⟨toGProc d, rfl, ⟨rfl, hsub⟩⟩
    | var x =>
        have hx : x ∈ S := hsub (by simp [recursiveVars])
        obtain ⟨b, hb, hbsub⟩ := hsup.2 x hx
        have hlab : (toGraph env root S hsup).label (varNode x) = toGProc b := by
          simp [hx, hb]
        exact ⟨varNode x, rfl, b, hb, ⟨hlab, hbsub⟩⟩
  · intro p gp hp
    obtain ⟨rfl, hsub⟩ := hp
    cases p with
    | deadlock => exact rfl
    | nSeq N d => exact ⟨d, rfl, ⟨rfl, hsub⟩⟩
    | recv x N d => exact ⟨d, rfl, ⟨rfl, hsub⟩⟩
    | send x N d => exact ⟨d, rfl, ⟨rfl, hsub⟩⟩
    | rcfgPrefix x N d => exact ⟨d, rfl, ⟨rfl, hsub⟩⟩
    | parallel a b =>
        have ha : recursiveVars a ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_left _ hz)
        have hb : recursiveVars b ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_right _ hz)
        exact ⟨a, b, rfl, ⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    | choice a b =>
        have ha : recursiveVars a ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_left _ hz)
        have hb : recursiveVars b ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_right _ hz)
        exact ⟨a, b, rfl, ⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    | leftMerge a b =>
        have ha : recursiveVars a ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_left _ hz)
        have hb : recursiveVars b ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_right _ hz)
        exact ⟨a, b, rfl, ⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    | commMerge a b =>
        have ha : recursiveVars a ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_left _ hz)
        have hb : recursiveVars b ⊆ S := by
          intro z hz
          exact hsub (by simp only [recursiveVars]; exact Finset.mem_union_right _ hz)
        exact ⟨a, b, rfl, ⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    | restrict L d => exact ⟨d, rfl, ⟨rfl, hsub⟩⟩
    | project n d => exact ⟨d, rfl, ⟨rfl, hsub⟩⟩
    | var x =>
        have hx : x ∈ S := hsub (by simp [recursiveVars])
        obtain ⟨b, hb, hbsub⟩ := hsup.2 x hx
        have hlab : (toGraph env root S hsup).label (varNode x) = toGProc b := by
          simp [hx, hb]
        exact ⟨x, b, rfl, hb, ⟨hlab, hbsub⟩⟩

/-- The root of the graph corresponds to the original process. -/
theorem toGraph_corr (env : RecEnv schema) (root : DyNetKAT schema) (S : Finset Var)
    (hsup : FiniteSupport env root S) :
    Corr (toGraph env root S hsup) env root (toGProc root) :=
  toGraph_corr_of_subset env root S hsup root hsup.1

/-- Successful compilation gives an unbounded two-way step correspondence. -/
theorem compileGraph_corr {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    {G : ProcessGraph schema} (h : compileGraph env root S = some G) :
    Corr G env root G.root := by
  obtain ⟨hs, rfl⟩ := compileGraph_eq_some_iff.mp h
  exact toGraph_corr env root S hs

------------------------------------------------------------------------
-- §6.1 Infinite reachable support prevents label-preserving compilation
--
-- The environment `infEnv` defines *every* variable `x` as `id; (x ++ "0")`,
-- so the variables reachable from `X` are `X`, `X0`, `X00`, … — infinitely
-- many distinct definitions.  No finite support set exists for it, hence
-- no finite graph can be constructed by `toGraph` from it.
------------------------------------------------------------------------

/-- The infinite-chain environment: every variable `x` is defined as
    `id; (x ++ "0")`. -/
def infEnv : RecEnv := fun x => some (.nSeq NetKAT.id (.var (x ++ "0")))

theorem infEnv_lookup (x : Var) :
    infEnv.lookup x = some (.nSeq NetKAT.id (.var (x ++ "0"))) := rfl

/-- The `n`-th variable of the infinite chain. -/
def chainVar : Nat → Var
  | 0 => "X"
  | n + 1 => chainVar n ++ "0"

theorem reachable_chainVar (n : Nat) : ReachableVar infEnv (.var "X") (chainVar n) := by
  induction n with
  | zero =>
      have h0 : chainVar 0 = "X" := rfl
      exact .direct (by rw [h0]; simp [recursiveVars])
  | succ n ih =>
      refine .throughDefinition ih (infEnv_lookup (chainVar n)) ?_
      show chainVar (n + 1) ∈ ({chainVar n ++ "0"} : Finset Var)
      have h1 : chainVar (n + 1) = chainVar n ++ "0" := rfl
      exact Finset.mem_singleton.mpr h1

theorem chainVar_length (n : Nat) : (chainVar n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h0 : ("0".length : Nat) = 1 := rfl
      have h1 : chainVar (n + 1) = chainVar n ++ "0" := rfl
      rw [h1, String.length_append, ih]
      omega

theorem chainVar_injective : Function.Injective chainVar := by
  intro n m h
  have hlen : (chainVar n).length = (chainVar m).length := by rw [h]
  rw [chainVar_length, chainVar_length] at hlen
  omega

/-- The infinite-chain environment admits no finite support set: every
    chain variable is reachable, the chain variables are pairwise distinct,
    and a finite support set would have to contain all of them. -/
theorem infEnv_no_finite_support (S : Finset Var) :
    ¬ FiniteSupport infEnv (.var "X") S := by
  intro hsup
  have hall : ∀ n, chainVar n ∈ S :=
    fun n => reachableVars_subset_of_finiteSupport infEnv (.var "X") S hsup _
      (reachable_chainVar n)
  have hsub : (Finset.range (S.card + 1)).image chainVar ⊆ S := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨n, _, rfl⟩ := hx
    exact hall n
  have hinj : ((Finset.range (S.card + 1)).image chainVar).card = S.card + 1 := by
    rw [Finset.card_image_of_injective _ chainVar_injective, Finset.card_range]
  have hle := Finset.card_le_card hsub
  omega

------------------------------------------------------------------------
-- §7 Finite execution traces and the bounded/unbounded distinction
------------------------------------------------------------------------

/-- Multi-step execution of the graph semantics. -/
inductive GSteps {schema : PacketSchema} (G : ProcessGraph schema) : GConfig schema → List (Action schema) → GConfig schema → Prop
  | nil (c : GConfig schema) : GSteps G c [] c
  | cons (c c' c'' : GConfig schema) (a : Action schema) (acts : List (Action schema))
      (h1 : GStep G c a c') (h2 : GSteps G c' acts c'') :
      GSteps G c (a :: acts) c''

/-- Trace soundness: every finite graph execution corresponds to a finite
    SOS execution with corresponding endpoints. -/
theorem gsteps_to_steps (G : ProcessGraph schema) (env : RecEnv schema) (gc gc' : GConfig schema)
    (acts : List (Action schema)) (hexec : GSteps G gc acts gc') :
    ∀ (p : DyNetKAT schema), Corr G env p gc.proc →
      ∃ (p' : DyNetKAT schema),
        Steps env
          (show (Config schema) from
            { proc := p, pending := gc.pending, handled := gc.handled }) acts
          (show (Config schema) from
            { proc := p', pending := gc'.pending, handled := gc'.handled }) ∧
        Corr G env p' gc'.proc := by
  induction hexec with
  | nil c =>
      intro p hcorr
      exact ⟨p, Steps.nil (show (Config schema) from
        { proc := p, pending := c.pending, handled := c.handled }), hcorr⟩
  | cons c c₁ c'' a rest h1 h2 ih =>
      intro p hcorr
      obtain ⟨p₁, hstep, hc₁⟩ := gstep_to_step G env c c₁ a h1 p hcorr
      obtain ⟨p', hrest, hc'⟩ := ih p₁ hc₁
      exact ⟨p', Steps.cons _ _ _ a rest hstep hrest, hc'⟩

/-- Trace completeness: every finite SOS execution corresponds to a finite
    graph execution with corresponding endpoints. -/
theorem steps_to_gsteps (G : ProcessGraph schema) (env : RecEnv schema) (c c' : Config schema)
    (acts : List (Action schema)) (hexec : Steps env c acts c') :
    ∀ (gp : GProc schema), Corr G env c.proc gp →
      ∃ (gp' : GProc schema),
        GSteps G
          (show (GConfig schema) from
            { proc := gp, pending := c.pending, handled := c.handled }) acts
          (show (GConfig schema) from
            { proc := gp', pending := c'.pending, handled := c'.handled }) ∧
        Corr G env c'.proc gp' := by
  induction hexec with
  | nil c =>
      intro gp hcorr
      exact ⟨gp, GSteps.nil (show (GConfig schema) from
        { proc := gp, pending := c.pending, handled := c.handled }), hcorr⟩
  | cons c c₁ c'' a rest h1 h2 ih =>
      intro gp hcorr
      obtain ⟨gp₁, hstep, hg₁⟩ := step_to_gstep G env c c₁ a h1 gp hcorr
      obtain ⟨gp', hrest, hg'⟩ := ih gp₁ hg₁
      exact ⟨gp', GSteps.cons _ _ _ a rest hstep hrest, hg'⟩

/-- Bounded SOS executions lift to the paper's projection `π_n`: a trace of
    length `≤ n` from `p` is a trace of `π_n(p)` (with the remaining budget
    recorded at the endpoint). -/
theorem steps_project_lift_aux {schema : PacketSchema} (env : RecEnv schema) (c c' : Config schema) (acts : List (Action schema))
    (hexec : Steps env c acts c') :
    ∀ (n : Nat), acts.length ≤ n →
    ∃ (j : Nat) (p' : DyNetKAT schema),
      c'.proc = p' ∧ j + acts.length = n ∧
      Steps env
        (show (Config schema) from
          { proc := .project n c.proc, pending := c.pending, handled := c.handled })
        acts
        (show (Config schema) from
          { proc := .project j p', pending := c'.pending, handled := c'.handled }) := by
  induction hexec with
  | nil c => intro n _; exact ⟨n, c.proc, rfl, by simp, Steps.nil _⟩
  | cons c c₁ c'' a rest h1 h2 ih =>
      intro n hn
      have hlen : (a :: rest).length = rest.length + 1 := rfl
      obtain ⟨m, rfl, hm⟩ : ∃ m, n = m + 1 ∧ rest.length ≤ m :=
        ⟨n - 1, by omega, by omega⟩
      have hproj : Step env
          (show (Config schema) from
            { proc := .project (m + 1) c.proc, pending := c.pending,
              handled := c.handled })
          a
          (show (Config schema) from
            { proc := .project m c₁.proc, pending := c₁.pending,
              handled := c₁.handled }) :=
        Step.cpol_project m c.proc c₁.proc a c.pending c₁.pending c.handled
          c₁.handled h1
      obtain ⟨j, p', hproc, hjeq, hrest⟩ := ih m hm
      refine ⟨j, p', hproc, ?_, Steps.cons _ _ _ a rest hproj hrest⟩
      rw [List.length_cons]
      omega

/-- The literal-form lift: a trace of length `≤ n` from `p` is a trace of
    `π_n(p)`. -/
theorem steps_project_lift {schema : PacketSchema} (env : RecEnv schema) (p : DyNetKAT schema) (pt hl : List schema.Packet)
    (acts : List (Action schema)) (c' : Config schema)
    (hexec : Steps env
      (show (Config schema) from { proc := p, pending := pt, handled := hl }) acts c')
    (n : Nat) (hn : acts.length ≤ n) :
    ∃ (j : Nat) (p' : DyNetKAT schema),
      c'.proc = p' ∧ j + acts.length = n ∧
      Steps env
        (show (Config schema) from
          { proc := .project n p, pending := pt, handled := hl }) acts
        (show (Config schema) from
          { proc := .project j p', pending := c'.pending, handled := c'.handled }) :=
  steps_project_lift_aux env { proc := p, pending := pt, handled := hl } c' acts
    hexec n hn

/-- Conversely, every trace of `π_n(p)` is a trace of `p`, and the
    endpoint keeps the remaining budget: this is the precise sense in
    which `π_n` observes exactly the first `n` steps. -/
theorem steps_project_unwrap {schema : PacketSchema} (env : RecEnv schema) :
    ∀ (acts : List (Action schema)) (n : Nat) (p : DyNetKAT schema) (pt hl : List schema.Packet)
      (q : DyNetKAT schema) (pt' hl' : List schema.Packet),
      Steps env
        (show (Config schema) from
          { proc := .project n p, pending := pt, handled := hl }) acts
        (show (Config schema) from
          { proc := q, pending := pt', handled := hl' }) →
      ∃ (j : Nat) (p' : DyNetKAT schema),
        q = .project j p' ∧ j + acts.length = n ∧
        Steps env
          (show (Config schema) from { proc := p, pending := pt, handled := hl }) acts
          (show (Config schema) from
            { proc := p', pending := pt', handled := hl' }) := by
  intro acts
  induction acts with
  | nil =>
      intro n p pt hl q pt' hl' hexec
      cases hexec with
      | nil c => exact ⟨n, p, rfl, by simp, Steps.nil _⟩
  | cons a rest ih =>
      intro n p pt hl q pt' hl' hexec
      cases hexec with
      | cons _ c₁ _ _ _ h1 h2 =>
        cases n with
        | zero => exact absurd h1 (project_zero_no_step env p pt hl a c₁)
        | succ k =>
            obtain ⟨q₁, pt₁, hl₁, hc₁⟩ : ∃ q₁ pt₁ hl₁,
                c₁ = (show (Config schema) from
                  { proc := q₁, pending := pt₁, handled := hl₁ }) :=
              ⟨c₁.proc, c₁.pending, c₁.handled, rfl⟩
            subst hc₁
            obtain ⟨p'', hp'', hstep⟩ :=
              project_step_inv env k p pt hl a q₁ pt₁ hl₁ h1
            rw [hp''] at h2
            obtain ⟨j, p', hq, hjeq, hrest⟩ := ih k p'' pt₁ hl₁ q pt' hl' h2
            refine ⟨j, p', hq, ?_, Steps.cons _ _ _ a rest hstep hrest⟩
            rw [List.length_cons]
            omega



------------------------------------------------------------------------
-- §8 Bounded graph exploration
------------------------------------------------------------------------

/-- Bounded graph reachability: `dst` is reachable from `src` in at most
    `n` graph transitions. -/
inductive GReachableWithin {schema : PacketSchema} (G : ProcessGraph schema) : Nat → GConfig schema → GConfig schema → Prop
  | refl (n : Nat) (c : GConfig schema) : GReachableWithin G n c c
  | step (n : Nat) (c c' c'' : GConfig schema) (a : Action schema)
      (h1 : GStep G c a c') (h2 : GReachableWithin G n c' c'') :
      GReachableWithin G (n + 1) c c''

/-- Monotonicity: reachability within `n` steps implies reachability
    within any larger budget. -/
theorem GReachableWithin.mono {G : ProcessGraph schema} :
    ∀ {n m : Nat} {c c' : GConfig schema}, n ≤ m →
      GReachableWithin G n c c' → GReachableWithin G m c c' := by
  intro n m c c' hnm h
  induction h generalizing m with
  | refl k c => exact GReachableWithin.refl m c
  | step k c c₁ c'' a h1 h2 ih =>
      rcases Nat.lt_or_ge (k + 1) m with hlt | hge
      · have hm1 : m = m - 1 + 1 := by omega
        rw [hm1]
        exact GReachableWithin.step (m - 1) c c₁ c'' a h1 (ih (by omega))
      · have hm : m = k + 1 := by omega
        subst hm
        exact GReachableWithin.step k c c₁ c'' a h1 (ih (Nat.le_refl k))

/-- Zero-depth cutoff: within zero steps only the source itself is
    reachable.  A zero-depth exploration says nothing about behavior
    beyond identity. -/
theorem GReachableWithin.zero_eq {G : ProcessGraph schema} {c c' : GConfig schema}
    (h : GReachableWithin G 0 c c') : c = c' := by
  cases h with
  | refl n c => rfl

/-- Composition: reachability budgets add along concatenated explorations. -/
theorem GReachableWithin.trans {G : ProcessGraph schema} :
    ∀ {n : Nat} {c c₁ : GConfig schema}, GReachableWithin G n c c₁ →
      ∀ {m : Nat} {c' : GConfig schema}, GReachableWithin G m c₁ c' →
      GReachableWithin G (n + m) c c' := by
  intro n c c₁ h1
  induction h1 with
  | refl k c => intro m c' h2; exact GReachableWithin.mono (by omega) h2
  | step k c c₂ c'' a hstep hrest ih =>
      intro m c' h2
      have hcomm : k + 1 + m = k + m + 1 := by omega
      rw [hcomm]
      exact GReachableWithin.step (k + m) c c₂ c' a hstep (ih h2)

/-- Every finite graph execution of length `≤ n` witnesses bounded
    reachability within `n`. -/
theorem gsteps_reachable_within {G : ProcessGraph schema} {gc gc' : GConfig schema}
    {acts : List (Action schema)} (hexec : GSteps G gc acts gc') :
    ∀ n, acts.length ≤ n → GReachableWithin G n gc gc' := by
  induction hexec with
  | nil c => intro n hn; exact GReachableWithin.refl n c
  | cons c c₁ c'' a rest h1 h2 ih =>
      intro n hn
      have hlen : (a :: rest).length = rest.length + 1 := rfl
      have hn1 : n = n - 1 + 1 := by omega
      rw [hn1]
      exact GReachableWithin.step (n - 1) c c₁ c'' a h1 (ih (n - 1) (by omega))

------------------------------------------------------------------------
-- §9 Cyclic graph bisimulation and unbounded transfer
--
-- A graph bisimulation is an ordinary bisimulation on the graph LTS.
-- The finite definition table represents cycles without unfolding.
-- The graph LTS may still have infinitely many process states.
-- The transfer theorems below lift graph
-- bisimilarity to genuine unbounded `Bisimilar env` of the original SOS.
------------------------------------------------------------------------

/-- A symmetric relation over graph processes that matches every graph
    transition while preserving both packet histories — the exact
    counterpart of `IsBisimulation env`, with `GStep` in place of
    `Step env` and no environment anywhere. -/
def IsGBisimulation (G : ProcessGraph schema) (R : GProc schema → GProc schema → Prop) : Prop :=
  (∀ gp gq, R gp gq → R gq gp) ∧
  ∀ gp gq, R gp gq →
    ∀ (pt hl : List schema.Packet) (a : Action schema) (gp' : GProc schema) (pt' hl' : List schema.Packet),
      GStep G
        (show (GConfig schema) from { proc := gp, pending := pt, handled := hl }) a
        (show (GConfig schema) from { proc := gp', pending := pt', handled := hl' }) →
      ∃ gq',
        GStep G
          (show (GConfig schema) from { proc := gq, pending := pt, handled := hl }) a
          (show (GConfig schema) from
            { proc := gq', pending := pt', handled := hl' }) ∧
        R gp' gq'

/-- Graph bisimilarity: related by some graph bisimulation. -/
def GBisimilar (G : ProcessGraph schema) (gp gq : GProc schema) : Prop :=
  ∃ R, IsGBisimulation G R ∧ R gp gq

theorem GBisimilar.refl (G : ProcessGraph schema) (gp : GProc schema) : GBisimilar G gp gp :=
  ⟨fun a b => a = b, by
    constructor
    · intro a b h; exact h.symm
    · intro a b h pt hl a' gp' pt' hl' hstep
      subst h
      exact ⟨gp', hstep, rfl⟩, rfl⟩

theorem GBisimilar.symm (G : ProcessGraph schema) {gp gq : GProc schema} (h : GBisimilar G gp gq) :
    GBisimilar G gq gp := by
  obtain ⟨R, hR, hgp⟩ := h
  exact ⟨R, hR, hR.1 gp gq hgp⟩

theorem gbisimilar_isGBisimulation (G : ProcessGraph schema) :
    IsGBisimulation G (GBisimilar G) := by
  refine ⟨fun _ _ h => GBisimilar.symm G h, ?_⟩
  rintro p q ⟨R, hR, hpq⟩ pt hl a p' pt' hl' hstep
  obtain ⟨q', hstep', hpq'⟩ := hR.2 p q hpq pt hl a p' pt' hl' hstep
  exact ⟨q', hstep', R, hR, hpq'⟩

theorem GBisimilar.trans (G : ProcessGraph schema) {p q r : GProc schema}
    (hpq : GBisimilar G p q) (hqr : GBisimilar G q r) :
    GBisimilar G p r := by
  let R : GProc schema → GProc schema → Prop := fun x z =>
    ∃ y, GBisimilar G x y ∧ GBisimilar G y z
  refine ⟨R, ⟨?_, ?_⟩, q, hpq, hqr⟩
  · rintro x z ⟨y, hxy, hyz⟩
    exact ⟨y, GBisimilar.symm G hyz, GBisimilar.symm G hxy⟩
  · rintro x z ⟨y, hxy, hyz⟩ pt hl a x' pt' hl' hstep
    have bisim := gbisimilar_isGBisimulation G
    obtain ⟨y', hy, hxy'⟩ := bisim.2 x y hxy pt hl a x' pt' hl' hstep
    obtain ⟨z', hz, hyz'⟩ := bisim.2 y z hyz pt hl a y' pt' hl' hy
    exact ⟨z', hz, y', hxy', hyz'⟩

/-- **Unbounded transfer**: a graph bisimulation between corresponding
    processes yields genuine unbounded bisimilarity in the original
    environment-indexed SOS.  The proof lifts the graph bisimulation
    through the correspondence; no bounded cutoff is involved anywhere. -/
theorem gbisimilar_transfer (G : ProcessGraph schema) (env : RecEnv schema) {gp gq : GProc schema}
    {p q : DyNetKAT schema} (hR : GBisimilar G gp gq) (hp : Corr G env p gp)
    (hq : Corr G env q gq) :
    Bisimilar env p q := by
  obtain ⟨R, hR, hRgp⟩ := hR
  obtain ⟨hRsym, hRstep⟩ := hR
  refine ⟨fun x y => ∃ gx gy, Corr G env x gx ∧ Corr G env y gy ∧ R gx gy, ?_, ⟨gp, gq, hp, hq, hRgp⟩⟩
  constructor
  · intro x y h
    obtain ⟨gx, gy, hx, hy, hR⟩ := h
    exact ⟨gy, gx, hy, hx, hRsym gx gy hR⟩
  · intro x y h pt hl a x' pt' hl' hstep
    obtain ⟨gx, gy, hx, hy, hR⟩ := h
    obtain ⟨gy₁, hgstep, hcx⟩ :=
      step_to_gstep G env ⟨x, pt, hl⟩ ⟨x', pt', hl'⟩ a hstep gx hx
    obtain ⟨gz', hgstep', hR'⟩ :=
      hRstep gx gy hR pt hl a gy₁ pt' hl' hgstep
    obtain ⟨y', hstep', hcy⟩ :=
      gstep_to_step G env ⟨gy, pt, hl⟩ ⟨gz', pt', hl'⟩ a hgstep' y hy
    exact ⟨y', hstep', ⟨gy₁, gz', hcx, hcy, hR'⟩⟩

/-- Bisimilarity is reflected and preserved for corresponding processes. -/
theorem gbisimilar_iff_bisimilar (G : ProcessGraph schema) (env : RecEnv schema)
    {p q : DyNetKAT schema} {gp gq : GProc schema} (hp : Corr G env p gp) (hq : Corr G env q gq) :
    GBisimilar G gp gq ↔ Bisimilar env p q := by
  refine ⟨fun h => gbisimilar_transfer G env h hp hq, ?_⟩
  rintro ⟨R, hR, hpq⟩
  refine ⟨fun x y => ∃ u v, Corr G env u x ∧ Corr G env v y ∧ R u v,
    ⟨?_, ?_⟩, p, q, hp, hq, hpq⟩
  · rintro x y ⟨u, v, hu, hv, huv⟩
    exact ⟨v, u, hv, hu, hR.1 u v huv⟩
  · rintro x y ⟨u, v, hu, hv, huv⟩ pt hl a x' pt' hl' hx
    obtain ⟨u', hu', hcx⟩ :=
      gstep_to_step G env ⟨x, pt, hl⟩ ⟨x', pt', hl'⟩ a hx u hu
    obtain ⟨v', hv', huv'⟩ := hR.2 u v huv pt hl a u' pt' hl' hu'
    obtain ⟨y', hy', hcy⟩ :=
      step_to_gstep G env ⟨v, pt, hl⟩ ⟨v', pt', hl'⟩ a hv' y hv
    exact ⟨y', hy', u', v', hcx, hcy, huv'⟩

theorem compileGraph_bisimilar_iff {env : RecEnv schema} {p q : DyNetKAT schema} {S : Finset Var}
    {G : ProcessGraph schema} (h : compileGraph env (.choice p q) S = some G) :
    GBisimilar G (toGProc p) (toGProc q) ↔ Bisimilar env p q := by
  obtain ⟨hs, rfl⟩ := compileGraph_eq_some_iff.mp h
  exact gbisimilar_iff_bisimilar _ env
    (toGraph_corr_of_subset _ _ _ hs p (fun _ hi => hs.1 (Finset.mem_union_left _ hi)))
    (toGraph_corr_of_subset _ _ _ hs q (fun _ hi => hs.1 (Finset.mem_union_right _ hi)))

/-- **Environment independence**: once the recursive variables are resolved
    into graph edges, the bisimilarity verdict no longer depends on the
    environment.  For a FIXED graph bisimulation `R gp gq`, EVERY
    environment under which `p` corresponds to `gp` and `q` to `gq` makes
    `p` and `q` bisimilar. -/
theorem graph_bisimulation_environment_independent (G : ProcessGraph schema)
    (R : GProc schema → GProc schema → Prop) (hR : IsGBisimulation G R) {gp gq : GProc schema}
    (hRgp : R gp gq) (env : RecEnv schema) (p q : DyNetKAT schema)
    (hp : Corr G env p gp) (hq : Corr G env q gq) :
    Bisimilar env p q :=
  gbisimilar_transfer G env ⟨R, hR, hRgp⟩ hp hq

/-- Cross-environment bisimulation: a relation between processes
    interpreted under two DIFFERENT environments such that `Step env₁`
    transitions of one side are matched by `Step env₂` transitions of the
    other and vice versa.  This is the standard bisimulation notion
    between two labeled transition systems; for `env₁ = env₂` the two
    conditions collapse to the usual symmetric matching. -/
def IsBisimulation2 (env₁ env₂ : RecEnv schema) (R : DyNetKAT schema → DyNetKAT schema → Prop) : Prop :=
  (∀ p q, R p q →
    ∀ (pt hl : List schema.Packet) (a : Action schema) (p' : DyNetKAT schema) (pt' hl' : List schema.Packet),
      Step env₁
        (show (Config schema) from { proc := p, pending := pt, handled := hl }) a
        (show (Config schema) from { proc := p', pending := pt', handled := hl' }) →
      ∃ q',
        Step env₂
          (show (Config schema) from { proc := q, pending := pt, handled := hl }) a
          (show (Config schema) from
            { proc := q', pending := pt', handled := hl' }) ∧
        R p' q') ∧
  (∀ p q, R p q →
    ∀ (pt hl : List schema.Packet) (a : Action schema) (q' : DyNetKAT schema) (pt' hl' : List schema.Packet),
      Step env₂
        (show (Config schema) from { proc := q, pending := pt, handled := hl }) a
        (show (Config schema) from { proc := q', pending := pt', handled := hl' }) →
      ∃ p',
        Step env₁
          (show (Config schema) from { proc := p, pending := pt, handled := hl }) a
          (show (Config schema) from
            { proc := p', pending := pt', handled := hl' }) ∧
        R p' q')

/-- For a single environment, the symmetric closure of a two-directional
    bisimulation is a genuine bisimulation, so related processes are
    `Bisimilar`. -/
theorem bisimilar_of_isBisimulation2_same_env {env : RecEnv schema} {p q : DyNetKAT schema}
    {R : DyNetKAT schema → DyNetKAT schema → Prop} (h : IsBisimulation2 env env R) (hpq : R p q) :
    Bisimilar env p q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x y => R x y ∨ R y x, ?_, Or.inl hpq⟩
  constructor
  · intro x y hxy
    rcases hxy with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro x y hxy pt hl a x' pt' hl' hstep
    rcases hxy with h | h
    · obtain ⟨y', hstep', hR'⟩ := h1 x y h pt hl a x' pt' hl' hstep
      exact ⟨y', hstep', Or.inl hR'⟩
    · obtain ⟨y', hstep', hR'⟩ := h2 y x h pt hl a x' pt' hl' hstep
      exact ⟨y', hstep', Or.inr hR'⟩

/-- **Cross-environment transfer**: the same finite graph bisimulation
    relates processes interpreted under two DIFFERENT environments, as
    long as each corresponds to its graph process.  This is the sharpest
    form of environment independence: the graph, not the environment,
    carries the meaning of the recursive variables. -/
theorem gbisimilar_transfer2 (G : ProcessGraph schema) {gp gq : GProc schema} {p q : DyNetKAT schema}
    (hR : GBisimilar G gp gq) (env₁ env₂ : RecEnv schema)
    (hp : Corr G env₁ p gp) (hq : Corr G env₂ q gq) :
    ∃ S, IsBisimulation2 env₁ env₂ S ∧ S p q := by
  obtain ⟨R, hR, hRgp⟩ := hR
  obtain ⟨hRsym, hRstep⟩ := hR
  refine ⟨fun x y => ∃ gx gy, Corr G env₁ x gx ∧ Corr G env₂ y gy ∧ R gx gy, ?_,
    ⟨gp, gq, hp, hq, hRgp⟩⟩
  constructor
  · intro x y h pt hl a x' pt' hl' hstep
    obtain ⟨gx, gy, hx, hy, hR⟩ := h
    obtain ⟨gy₁, hgstep, hcx⟩ :=
      step_to_gstep G env₁ ⟨x, pt, hl⟩ ⟨x', pt', hl'⟩ a hstep gx hx
    obtain ⟨gz', hgstep', hR'⟩ :=
      hRstep gx gy hR pt hl a gy₁ pt' hl' hgstep
    obtain ⟨y', hstep', hcy⟩ :=
      gstep_to_step G env₂ ⟨gy, pt, hl⟩ ⟨gz', pt', hl'⟩ a hgstep' y hy
    exact ⟨y', hstep', ⟨gy₁, gz', hcx, hcy, hR'⟩⟩
  · intro x y h pt hl a y' pt' hl' hstep
    obtain ⟨gx, gy, hx, hy, hR⟩ := h
    obtain ⟨gz₁, hgstep, hcy⟩ :=
      step_to_gstep G env₂ ⟨y, pt, hl⟩ ⟨y', pt', hl'⟩ a hstep gy hy
    obtain ⟨gy₂, hgstep', hR'⟩ :=
      hRstep gy gx (hRsym gx gy hR) pt hl a gz₁ pt' hl' hgstep
    obtain ⟨x', hstep', hcx⟩ :=
      gstep_to_step G env₁ ⟨gx, pt, hl⟩ ⟨gy₂, pt', hl'⟩ a hgstep' x hx
    exact ⟨x', hstep', ⟨gy₂, gz₁, hcx, hcy, hRsym gz₁ gy₂ hR'⟩⟩

------------------------------------------------------------------------
-- §9.5 Inversion lemmas for concrete graph steps
--
-- These decompose a graph step whose source process is a node reference
-- or a prefix, with all constructor unification done inside the lemma.
------------------------------------------------------------------------

/-- A graph step of a `ref` node is exactly a step of the node label. -/
theorem gstep_ref_inv {G : ProcessGraph schema} {i : NodeId} {pt hl : List schema.Packet}
    {a : Action schema} {gp' : GProc schema} {pt' hl' : List schema.Packet}
    (h : GStep G
      (show (GConfig schema) from
        { proc := .ref i, pending := pt, handled := hl }) a
      (show (GConfig schema) from
        { proc := gp', pending := pt', handled := hl' })) :
    GStep G
      (show (GConfig schema) from
        { proc := G.label i, pending := pt, handled := hl }) a
      (show (GConfig schema) from
        { proc := gp', pending := pt', handled := hl' }) := by
  cases h with
  | var _ _ _ _ _ _ _ step => exact step

/-- A graph step of an `nSeq` term is a packet step onto the continuation:
    no other Figure 8 rule applies to a bare `N; D`. -/
theorem gstep_nSeq_inv {G : ProcessGraph schema} {N : NetKAT schema} {cont : GProc schema}
    {pt hl : List schema.Packet} {a : Action schema} {gp' : GProc schema} {pt' hl' : List schema.Packet}
    (h : GStep G
      (show (GConfig schema) from
        { proc := .nSeq N cont, pending := pt, handled := hl }) a
      (show (GConfig schema) from
        { proc := gp', pending := pt', handled := hl' })) :
    ∃ σ σ' pt₀, pt = σ :: pt₀ ∧ a = Action.packet σ σ' ∧
      gp' = cont ∧ pt' = pt₀ ∧ hl' = σ' :: hl ∧
      HistorySemantics N (History.singleton σ) (History.singleton σ') := by
  cases h with
  | seq_ok _ _ σ σ' _ _ ev =>
      exact ⟨σ, σ', pt', rfl, rfl, rfl, rfl, rfl, ev⟩

------------------------------------------------------------------------
-- §10 Stuck unguarded cycles: the SOS and the graph agree behaviorally
--
-- For the unguarded mutual definition `X ≜ Y`, `Y ≜ X` neither the SOS
-- nor the graph admits any transition (`cpol_var` needs a transition of
-- the body, and the body chain never leaves the variables; likewise the
-- graph `ref` edges form a cycle with no prefix).  The no-step theorems
-- below are proved by induction on the transition derivation with the
-- source generalized to the two variables / two nodes.
------------------------------------------------------------------------

theorem no_step_var_two_cycle (env : RecEnv schema) (X Y : Var)
    (hX : env.lookup X = some (.var Y)) (hY : env.lookup Y = some (.var X))
    (pt hl : List schema.Packet) (a : Action schema) (dst : Config schema) :
    ¬ Step env
      (show (Config schema) from { proc := .var X, pending := pt, handled := hl }) a dst := by
  have general : ∀ (c : Config schema) (a' : Action schema) (dst' : Config schema),
      Step env c a' dst' →
      (c.proc = .var X ∨ c.proc = .var Y) → False := by
    intro c a' dst' hstep
    induction hstep with
    | cpol_seq_ok N q σ σ' pendingTail handled evaluates =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_choice_l p q p' a' pt₀ pt' hl₀ hl' steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_choice_r p q q' a' pt₀ pt' hl₀ hl' steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_par_l p q p' a' pt₀ pt' hl₀ hl' steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_par_r p q q' a' pt₀ pt' hl₀ hl' steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_left_merge p q p' a' pt₀ pt' hl₀ hl' steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_comm_merge_recv_send x r q s q' s' pt₀ hl₀ recv_step send_step =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_comm_merge_send_recv x r q s q' s' pt₀ hl₀ send_step recv_step =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_recv x N cont pt₀ hl₀ =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_send x N cont pt₀ hl₀ =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_rcfg x N cont pt₀ hl₀ =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_var name body body' a' pt₀ pt' hl₀ hl' definition step ih =>
        intro hproc
        simp at hproc
        rcases hproc with rfl | rfl
        · rw [hX] at definition
          have hbody : .var Y = body := Option.some.inj definition
          subst hbody
          exact ih (Or.inr rfl)
        · rw [hY] at definition
          have hbody : .var X = body := Option.some.inj definition
          subst hbody
          exact ih (Or.inl rfl)
    | cpol_sync_recv_send x r q s q' s' pt₀ hl₀ recv_step send_step =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_sync_send_recv x r q s q' s' pt₀ hl₀ send_step recv_step =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_project n p p' a' pt₀ pt' hl₀ hl' steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | cpol_restrict L p p' a' pt₀ pt' hl₀ hl' allowed steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
  intro hstep
  exact general _ _ _ hstep (Or.inl rfl)

theorem no_gstep_ref_two_cycle (G : ProcessGraph schema) (i j : NodeId)
    (hi : G.label i = .ref j) (hj : G.label j = .ref i)
    (pt hl : List schema.Packet) (a : Action schema) (dst : GConfig schema) :
    ¬ GStep G
      (show (GConfig schema) from { proc := .ref i, pending := pt, handled := hl }) a dst := by
  have general : ∀ (c : GConfig schema) (a' : Action schema) (dst' : GConfig schema),
      GStep G c a' dst' →
      (c.proc = .ref i ∨ c.proc = .ref j) → False := by
    intro c a' dst' hstep
    induction hstep with
    | seq_ok N cont σ σ' pt₀ hl₀ evaluates =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | choice_l gp gq gp' a' pt₀ pt' hl₀ hl' steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | choice_r gp gq gq' a' pt₀ pt' hl₀ hl' steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | par_l gp gq gp' a' pt₀ pt' hl₀ hl' steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | par_r gp gq gq' a' pt₀ pt' hl₀ hl' steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | left_merge gp gq gp' a' pt₀ pt' hl₀ hl' steps ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | comm_merge_recv_send x r gp gs gp' gs' pt₀ hl₀ recv_step send_step =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | comm_merge_send_recv x r gp gs gp' gs' pt₀ hl₀ send_step recv_step =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | recv x N cont pt₀ hl₀ =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | send x N cont pt₀ hl₀ =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | rcfg x N cont pt₀ hl₀ =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | var k gp' a' pt₀ pt' hl₀ hl' step ih =>
        intro hproc
        simp at hproc
        rcases hproc with rfl | rfl
        · rw [hi] at step
          exact ih (Or.inr hi)
        · rw [hj] at step
          exact ih (Or.inl hj)
    | sync_recv_send x r gp gs gp' gs' pt₀ hl₀ recv_step send_step =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | sync_send_recv x r gp gs gp' gs' pt₀ hl₀ send_step recv_step =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | project n gp gp' a' pt₀ pt' hl₀ hl' step ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
    | restrict L gp gp' a' pt₀ pt' hl₀ hl' allowed step ih =>
        intro hproc
        rcases hproc with h | h <;> simp at h
  intro hstep
  exact general _ _ _ hstep (Or.inl rfl)

end DyNetKAT.DyNetKAT
