------------------------------------------------------------------------
-- S6B — Graph-native head extraction for recursive DyNetKAT processes
--
-- Paper grounding (DyNetKAT paper, arXiv:2102.10035v4, §V, Eqs. (29)-(32)):
--   head(⊥)            = 0                    (29)
--   head(N;D)          = N + head(D)          (30)
--   head(D ⊕ Q)        = head(D) + head(Q)    (31)
--   head(rcfg_{X,N};D) = 0                    (32)
--
-- The AST-level `head` of S4A (`SafetyHead.lean`) fails on recursive
-- variables (`head (var X) = none`).  This module lifts `head` to the
-- finite recursive process graphs of S6A (`ProcessGraph.lean`), where
-- recursive variables are `GProc.ref` edges into a finite node set and
-- recursive definitions are cycles — so the head policy of
--
--   X ≜ N;X,      X ≜ N;Y,  Y ≜ M;X,      X ≜ Y,  Y ≜ X
--
-- is computed from the FINITE graph without infinite unfolding:
--
--   * `headRefsList` discovers the node references occurring in the
--     head region of a graph term (packet-prefix continuations and
--     choice branches are followed; reconfiguration boundaries,
--     communication prefixes, merges, restriction and projection do
--     not expose their descendants to the graph traversal).  Every
--     discovered reference is a `gprocRefs` member
--     (`headRefsList_subset_gprocRefs`), so `root_closed` and `closed`
--     can be used safely through this function.
--   * `RefReach` is node-level head reachability through reference
--     edges; it coincides with term-level `HeadPathTo` from a
--     reference (`refReach_iff_headPathTo`).
--   * `headRun` is the cycle-safe worklist traversal: a `List NodeId`
--     of pending nodes, a `Finset NodeId` of visited nodes, and
--     membership validation against `ProcessGraph.nodes`.  A visited
--     node is skipped, a node outside `G.nodes` fails explicitly, and
--     termination is by the lexicographic measure
--     (number of unvisited graph nodes, pending worklist length).
--     The visited set only ever contains verified nodes of `G.nodes`.
--   * `headCollect` collects the LOCAL NetKAT policy of a graph term
--     (paper Eqs. (29)-(31)): packet prefixes contribute their policy,
--     ⊥ and reconfiguration prefixes contribute `.drop`, choice unions
--     the branches, and a reference contributes `.drop` locally —
--     references are NEVER followed here.  Unsupported constructors
--     (`recv`, `send`, `parallel`, `leftMerge`, `commMerge`,
--     `restrict`, `project`) fail explicitly with `none`.
--   * `graphHead G` collects the root's local policy, discovers all
--     head-reachable nodes with the worklist, visits each exactly
--     once, collects each node label's local policy, and combines
--     everything with `NetKAT.union`.  Unreachable definitions are
--     never enumerated, and extraction failure (`none`) is distinct
--     from the empty policy (`some .drop`).
--   * `graphHead_sound` (S6B Part 3A) — semantic soundness of the
--     extraction w.r.t. the relational specification: whenever
--     `graphHead G = some H`, the semantics of `H` is included in the
--     behavior described by `GraphHeadSpec G G.root`.  Cycles are
--     handled by the worklist's exactly-once visiting: every
--     contribution comes from a head-reachable node's label, and a
--     reference contributes `.drop` locally, so cyclic references
--     neither duplicate nor fabricate contributions.
--   * `graphHead_complete` (S6B Part 3B) — semantic completeness, the
--     converse inclusion: whenever `graphHead G = some H`, every packet
--     pair described by `GraphHeadSpec G G.root` lies in the semantics
--     of `H`.  No supportedness hypothesis is needed beyond the success
--     itself (success already forces every involved local collection to
--     succeed); supportedness is only needed to GUARANTEE that some `H`
--     exists (`graphHead_supported_some`), which yields the packaged
--     specification equivalence `graphHead_spec_iff`.
--
-- Termination: `headCollect` and `headRefsList` are structurally
-- recursive (references are never followed during collection), and
-- `headRun` is well-founded recursive on the lexicographic measure
-- `((G.nodes \ visited).card, pending.length)`; the first component
-- strictly decreases whenever a fresh node of `G.nodes` is visited
-- (the visited set stays inside `G.nodes`), and the second strictly
-- decreases whenever a pending node is skipped.  No `partial`, no
-- `unsafe`, no arbitrary fuel, no `Classical.choice`, no `sorry`.
--
-- Scope boundary: this module implements the executable extraction,
-- its supportedness theorem, the relational graph-head specification
-- (`GraphHeadSpec`), the semantic soundness of the extraction against
-- that specification (`graphHead_sound`, S6B Part 3A), and its semantic
-- completeness (`graphHead_complete`, S6B Part 3B), packaged into the
-- specification equivalence `graphHead_spec_iff`.  It does NOT prove
-- compatibility with the S4A AST-level `head`, does NOT implement graph
-- tail extraction (S6C), and does not integrate the recursive safety
-- checker (S6D).
------------------------------------------------------------------------

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Card
import NetKATLean.Core.Packet
import NetKATLean.Core.Semantics
import NetKATLean.Core.Decision
import DyNetKATLean.Core.AST
import DyNetKATLean.Core.RecEnv
import DyNetKATLean.Core.SafetyHead
import DyNetKATLean.Core.ProcessGraph

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : NetKAT.PacketSchema}

open DyNetKAT.NetKAT

------------------------------------------------------------------------
-- §1 The head region of a graph term
--
-- `headRefs gp` is the finite set of node references reachable from the
-- term `gp` before any reconfiguration boundary or unsupported
-- constructor: packet-prefix continuations and choice branches are
-- followed, `rcfgPrefix`/`recv`/`send`/`parallel`/`leftMerge`/
-- `commMerge`/`restrict`/`project`/`deadlock` stop the traversal, and a
-- reference `ref i` contributes `{i}` without following the label
-- (following labels is the job of the reachability iteration, which is
-- where termination is handled).
------------------------------------------------------------------------

/-- The node references occurring in the head region of a graph term. -/
def headRefs : GProc schema → Finset NodeId
  | .deadlock => ∅
  | .nSeq _ cont => headRefs cont
  | .recv _ _ _ => ∅
  | .send _ _ _ => ∅
  | .rcfgPrefix _ _ _ => ∅
  | .parallel _ _ => ∅
  | .choice a b => headRefs a ∪ headRefs b
  | .leftMerge _ _ => ∅
  | .commMerge _ _ => ∅
  | .restrict _ _ => ∅
  | .project _ _ => ∅
  | .ref i => {i}

/-- Defining equations of `headRefs`. -/
theorem headRefs_nSeq (N : NetKAT schema) (cont : GProc schema) :
    headRefs (.nSeq N cont) = headRefs cont := rfl

theorem headRefs_choice (a b : GProc schema) :
    headRefs (.choice a b) = headRefs a ∪ headRefs b := rfl

theorem headRefs_ref (i : NodeId) : headRefs (schema := schema) (.ref i) = {i} := rfl

theorem headRefs_rcfgPrefix (x : Channel) (N : NetKAT schema) (cont : GProc schema) :
    headRefs (.rcfgPrefix x N cont) = ∅ := rfl

theorem headRefs_recv (x : Channel) (N : NetKAT schema) (cont : GProc schema) :
    headRefs (.recv x N cont) = ∅ := rfl

theorem headRefs_send (x : Channel) (N : NetKAT schema) (cont : GProc schema) :
    headRefs (.send x N cont) = ∅ := rfl

theorem headRefs_parallel (a b : GProc schema) : headRefs (.parallel a b) = ∅ := rfl

theorem headRefs_leftMerge (a b : GProc schema) : headRefs (.leftMerge a b) = ∅ := rfl

theorem headRefs_commMerge (a b : GProc schema) : headRefs (.commMerge a b) = ∅ := rfl

theorem headRefs_restrict (L : Set (CommunicationAction schema)) (cont : GProc schema) :
    headRefs (.restrict L cont) = ∅ := rfl

theorem headRefs_project (n : Nat) (cont : GProc schema) :
    headRefs (.project n cont) = ∅ := rfl

theorem headRefs_deadlock : headRefs (schema := schema) .deadlock = ∅ := rfl

/-- The head region is contained in the full reference set, so every
    head reference of a well-formed graph term is a live node. -/
theorem headRefs_le_gprocRefs (gp : GProc schema) : headRefs gp ⊆ gprocRefs gp := by
  cases gp with
  | deadlock => exact Finset.Subset.rfl
  | nSeq N cont => exact headRefs_le_gprocRefs cont
  | recv x N cont => exact Finset.empty_subset _
  | send x N cont => exact Finset.empty_subset _
  | rcfgPrefix x N cont => exact Finset.empty_subset _
  | parallel a b => exact Finset.empty_subset _
  | choice a b =>
      intro i hi
      simp only [headRefs, Finset.mem_union] at hi
      simp only [gprocRefs, Finset.mem_union]
      rcases hi with hi | hi
      · exact Or.inl (headRefs_le_gprocRefs a hi)
      · exact Or.inr (headRefs_le_gprocRefs b hi)
  | leftMerge a b => exact Finset.empty_subset _
  | commMerge a b => exact Finset.empty_subset _
  | restrict L cont => exact Finset.empty_subset _
  | project n cont => exact Finset.empty_subset _
  | ref i => exact Finset.Subset.rfl

------------------------------------------------------------------------
-- §1.1 Head-region term containment
--
-- `HeadSub G ct gp`: the term `gp` occurs in the head region of the
-- term `ct` (packet-prefix continuations, choice branches, and
-- reference edges into node labels).  `HeadSubFree` is the ref-free
-- fragment: containment without crossing any reference edge.  Both are
-- least-fixpoint inductive relations, so cyclic graphs are handled by
-- finite derivations.
------------------------------------------------------------------------

/-- `gp` occurs in the head region of `ct`. -/
inductive HeadSub {schema : NetKAT.PacketSchema} (G : ProcessGraph schema) : GProc schema → GProc schema → Prop
  | refl (gp : GProc schema) : HeadSub G gp gp
  | nSeq (N : NetKAT schema) (cont sub : GProc schema) (h : HeadSub G cont sub) :
      HeadSub G (.nSeq N cont) sub
  | choice_left (a b sub : GProc schema) (h : HeadSub G a sub) :
      HeadSub G (.choice a b) sub
  | choice_right (a b sub : GProc schema) (h : HeadSub G b sub) :
      HeadSub G (.choice a b) sub
  | ref (i : NodeId) (sub : GProc schema) (h : HeadSub G (G.label i) sub) :
      HeadSub G (.ref i) sub

/-- `gp` occurs in the head region of `ct` without crossing any
    reference edge. -/
inductive HeadSubFree {schema : NetKAT.PacketSchema} (G : ProcessGraph schema) : GProc schema → GProc schema → Prop
  | refl (gp : GProc schema) : HeadSubFree G gp gp
  | nSeq (N : NetKAT schema) (cont sub : GProc schema) (h : HeadSubFree G cont sub) :
      HeadSubFree G (.nSeq N cont) sub
  | choice_left (a b sub : GProc schema) (h : HeadSubFree G a sub) :
      HeadSubFree G (.choice a b) sub
  | choice_right (a b sub : GProc schema) (h : HeadSubFree G b sub) :
      HeadSubFree G (.choice a b) sub

/-- Head-subterm containment composes. -/
theorem HeadSub.trans {G : ProcessGraph schema} {a b c : GProc schema}
    (h1 : HeadSub G a b) (h2 : HeadSub G b c) : HeadSub G a c := by
  induction h1 with
  | refl gp => exact h2
  | nSeq N cont sub _ ih => exact HeadSub.nSeq N cont c (ih h2)
  | choice_left a b sub _ ih => exact HeadSub.choice_left a b c (ih h2)
  | choice_right a b sub _ ih => exact HeadSub.choice_right a b c (ih h2)
  | ref i sub _ ih => exact HeadSub.ref i c (ih h2)

/-- Inversion: a head-subterm of `N; cont` is the term itself or a
    head-subterm of `cont`. -/
theorem headSub_nSeq_inv {G : ProcessGraph schema} {N : NetKAT schema} {cont sub : GProc schema}
    (h : HeadSub G (.nSeq N cont) sub) :
    sub = .nSeq N cont ∨ HeadSub G cont sub := by
  cases h with
  | refl gp => exact Or.inl rfl
  | nSeq N cont sub h' => exact Or.inr h'

/-- Inversion: a head-subterm of `a ⊕ b` is the term itself or a
    head-subterm of one branch. -/
theorem headSub_choice_inv {G : ProcessGraph schema} {a b sub : GProc schema}
    (h : HeadSub G (.choice a b) sub) :
    sub = .choice a b ∨ HeadSub G a sub ∨ HeadSub G b sub := by
  cases h with
  | refl gp => exact Or.inl rfl
  | choice_left a b sub h' => exact Or.inr (Or.inl h')
  | choice_right a b sub h' => exact Or.inr (Or.inr h')

/-- Inversion: a head-subterm of `ref i` is the term itself or a
    head-subterm of the node label. -/
theorem headSub_ref_inv {G : ProcessGraph schema} {i : NodeId} {sub : GProc schema}
    (h : HeadSub G (.ref i) sub) :
    sub = .ref i ∨ HeadSub G (G.label i) sub := by
  cases h with
  | refl gp => exact Or.inl rfl
  | ref i sub h' => exact Or.inr h'

/-- Inversion for the ref-free containment of an `nSeq` term. -/
theorem headSubFree_nSeq_inv {G : ProcessGraph schema} {N : NetKAT schema} {cont sub : GProc schema}
    (h : HeadSubFree G (.nSeq N cont) sub) :
    sub = .nSeq N cont ∨ HeadSubFree G cont sub := by
  cases h with
  | refl gp => exact Or.inl rfl
  | nSeq N cont sub h' => exact Or.inr h'

/-- Inversion for the ref-free containment of a `choice` term. -/
theorem headSubFree_choice_inv {G : ProcessGraph schema} {a b sub : GProc schema}
    (h : HeadSubFree G (.choice a b) sub) :
    sub = .choice a b ∨ HeadSubFree G a sub ∨ HeadSubFree G b sub := by
  cases h with
  | refl gp => exact Or.inl rfl
  | choice_left a b sub h' => exact Or.inr (Or.inl h')
  | choice_right a b sub h' => exact Or.inr (Or.inr h')

/-- The head references of a ref-free head-subterm are contained in the
    head references of the containing term. -/
theorem headRefs_mono_subFree {G : ProcessGraph schema} {ct gp : GProc schema}
    (h : HeadSubFree G ct gp) : headRefs gp ⊆ headRefs ct := by
  induction h with
  | refl gp => exact Finset.Subset.rfl
  | nSeq N cont sub _ ih => exact ih
  | choice_left a b sub _ ih =>
      intro i hi
      simp only [headRefs, Finset.mem_union]
      exact Or.inl (ih hi)
  | choice_right a b sub _ ih =>
      intro i hi
      simp only [headRefs, Finset.mem_union]
      exact Or.inr (ih hi)

------------------------------------------------------------------------
-- §1.2 Head-prefix occurrence
--
-- `HeadPrefixOf G gp N`: the NetKAT policy `N` occurs at a
-- packet-processing prefix position reachable from the term `gp`
-- before any reconfiguration boundary.  This is the graph-level
-- counterpart of the positions collected by the paper's `head`
-- equations (30)-(31); reconfiguration prefixes (32) and unsupported
-- constructors contribute no constructors, so the relation is empty
-- below them.
------------------------------------------------------------------------

/-- `N` occurs at a packet-prefix position in the head region of `gp`. -/
inductive HeadPrefixOf {schema : NetKAT.PacketSchema} (G : ProcessGraph schema) : GProc schema → NetKAT schema → Prop
  | here (N : NetKAT schema) (cont : GProc schema) : HeadPrefixOf G (.nSeq N cont) N
  | nSeq (N : NetKAT schema) (cont : GProc schema) (M : NetKAT schema)
      (h : HeadPrefixOf G cont M) : HeadPrefixOf G (.nSeq N cont) M
  | choice_left (a b : GProc schema) (M : NetKAT schema)
      (h : HeadPrefixOf G a M) : HeadPrefixOf G (.choice a b) M
  | choice_right (a b : GProc schema) (M : NetKAT schema)
      (h : HeadPrefixOf G b M) : HeadPrefixOf G (.choice a b) M
  | ref (i : NodeId) (M : NetKAT schema)
      (h : HeadPrefixOf G (G.label i) M) : HeadPrefixOf G (.ref i) M

/-- Helper for the prefix-occurrence characterization: a head-subterm
    of the shape `N; cont` witnesses a prefix occurrence. -/
theorem headPrefixOf_of_headSub (G : ProcessGraph schema) :
    ∀ (gp sub : GProc schema), HeadSub G gp sub →
      ∀ (N : NetKAT schema) (cont : GProc schema), sub = .nSeq N cont →
        HeadPrefixOf G gp N := by
  intro gp sub hs
  induction hs with
  | refl gp =>
      intro N cont heq
      subst heq
      exact HeadPrefixOf.here N cont
  | nSeq N' cont' sub' _ ih =>
      intro N cont heq
      exact HeadPrefixOf.nSeq N' cont' N (ih N cont heq)
  | choice_left a b sub' _ ih =>
      intro N cont heq
      exact HeadPrefixOf.choice_left a b N (ih N cont heq)
  | choice_right a b sub' _ ih =>
      intro N cont heq
      exact HeadPrefixOf.choice_right a b N (ih N cont heq)
  | ref i sub' _ ih =>
      intro N cont heq
      exact HeadPrefixOf.ref i N (ih N cont heq)

/-- A prefix occurrence at `gp` is witnessed by a head-subterm of the
    shape `N; cont`. -/
theorem headPrefixOf_iff_headSub (G : ProcessGraph schema) (gp : GProc schema) (N : NetKAT schema) :
    HeadPrefixOf G gp N ↔ ∃ cont : GProc schema, HeadSub G gp (.nSeq N cont) := by
  constructor
  · intro h
    induction h with
    | here N cont => exact ⟨cont, HeadSub.refl (.nSeq N cont)⟩
    | nSeq N cont M _ ih =>
        obtain ⟨cont'', hs⟩ := ih
        exact ⟨cont'', HeadSub.nSeq N cont (.nSeq M cont'') hs⟩
    | choice_left a b M _ ih =>
        obtain ⟨cont'', hs⟩ := ih
        exact ⟨cont'', HeadSub.choice_left a b (.nSeq M cont'') hs⟩
    | choice_right a b M _ ih =>
        obtain ⟨cont'', hs⟩ := ih
        exact ⟨cont'', HeadSub.choice_right a b (.nSeq M cont'') hs⟩
    | ref i M _ ih =>
        obtain ⟨cont'', hs⟩ := ih
        exact ⟨cont'', HeadSub.ref i (.nSeq M cont'') hs⟩
  · rintro ⟨cont, hs⟩
    exact headPrefixOf_of_headSub G gp (.nSeq N cont) hs N cont rfl

------------------------------------------------------------------------
-- §1.3 Head reachability of nodes
--
-- `HeadPathTo G gp j`: the node `j` is reachable from the term `gp` in
-- the head region, i.e. its reference occurs at a position reachable
-- from `gp` before any reconfiguration boundary.  Recursive cycles
-- yield finite derivations (the `ref_step` rule follows the edge into
-- the node label without unfolding it).
------------------------------------------------------------------------

/-- Node `j` is head-reachable from the term `gp`. -/
inductive HeadPathTo {schema : NetKAT.PacketSchema} (G : ProcessGraph schema) : GProc schema → NodeId → Prop
  | ref (i : NodeId) : HeadPathTo G (.ref i) i
  | nSeq (N : NetKAT schema) (cont : GProc schema) (j : NodeId)
      (h : HeadPathTo G cont j) : HeadPathTo G (.nSeq N cont) j
  | choice_left (a b : GProc schema) (j : NodeId)
      (h : HeadPathTo G a j) : HeadPathTo G (.choice a b) j
  | choice_right (a b : GProc schema) (j : NodeId)
      (h : HeadPathTo G b j) : HeadPathTo G (.choice a b) j
  | ref_step (i j : NodeId) (h : HeadPathTo G (G.label i) j) :
      HeadPathTo G (.ref i) j

/-- Every head reference of a term is head-reachable from it. -/
theorem headRefs_pathTo (G : ProcessGraph schema) :
    ∀ (gp : GProc schema) (i : NodeId), i ∈ headRefs gp → HeadPathTo G gp i := by
  intro gp
  cases gp with
  | deadlock => intro i hi; simp [headRefs] at hi
  | nSeq N cont =>
      intro i hi
      simp only [headRefs] at hi
      exact HeadPathTo.nSeq N cont i (headRefs_pathTo G cont i hi)
  | recv x N cont => intro i hi; simp [headRefs] at hi
  | send x N cont => intro i hi; simp [headRefs] at hi
  | rcfgPrefix x N cont => intro i hi; simp [headRefs] at hi
  | parallel a b => intro i hi; simp [headRefs] at hi
  | choice a b =>
      intro i hi
      simp only [headRefs, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact HeadPathTo.choice_left a b i (headRefs_pathTo G a i hi)
      · exact HeadPathTo.choice_right a b i (headRefs_pathTo G b i hi)
  | leftMerge a b => intro i hi; simp [headRefs] at hi
  | commMerge a b => intro i hi; simp [headRefs] at hi
  | restrict L cont => intro i hi; simp [headRefs] at hi
  | project n cont => intro i hi; simp [headRefs] at hi
  | ref i =>
      intro j hj
      simp only [headRefs, Finset.mem_singleton] at hj
      subst hj
      exact HeadPathTo.ref _

/-- Head reachability composes through a node label: if `j` is
    reachable from `gp` and `i` is reachable from the label of `j`,
    then `i` is reachable from `gp`. -/
theorem headPathTo_trans {G : ProcessGraph schema} {gp : GProc schema} {j i : NodeId}
    (h1 : HeadPathTo G gp j) (h2 : HeadPathTo G (G.label j) i) :
    HeadPathTo G gp i := by
  induction h1 with
  | ref k => exact HeadPathTo.ref_step k i h2
  | nSeq N cont k _ ih => exact HeadPathTo.nSeq N cont i (ih h2)
  | choice_left a b k _ ih => exact HeadPathTo.choice_left a b i (ih h2)
  | choice_right a b k _ ih => exact HeadPathTo.choice_right a b i (ih h2)
  | ref_step k l _ ih => exact HeadPathTo.ref_step k i (ih h2)

/-- A node reachable from `gp` has its label inside the head region of
    `gp` (as a term). -/
theorem headPathTo_sub {G : ProcessGraph schema} {gp : GProc schema} {j : NodeId}
    (h : HeadPathTo G gp j) : HeadSub G gp (G.label j) := by
  induction h with
  | ref i => exact HeadSub.ref i (G.label i) (HeadSub.refl (G.label i))
  | nSeq N cont k _ ih => exact HeadSub.nSeq N cont (G.label k) ih
  | choice_left a b k _ ih => exact HeadSub.choice_left a b (G.label k) ih
  | choice_right a b k _ ih => exact HeadSub.choice_right a b (G.label k) ih
  | ref_step i k _ ih => exact HeadSub.ref i (G.label k) ih

------------------------------------------------------------------------
-- §2 Head-reference discovery
--
-- `headRefsList` is the structurally recursive, computable list of the
-- node references occurring in the head region of a graph term.  It
-- inspects only the positions relevant to head extraction:
-- packet-prefix continuations and choice branches are followed, while
-- reconfiguration boundaries, communication prefixes, merges,
-- restriction and projection do not expose their descendants to the
-- graph traversal.
------------------------------------------------------------------------

/-- List-valued counterpart of `headRefs` (structurally recursive,
    computable). -/
def headRefsList : GProc schema → List NodeId
  | .deadlock => []
  | .nSeq _ cont => headRefsList cont
  | .recv _ _ _ => []
  | .send _ _ _ => []
  | .rcfgPrefix _ _ _ => []
  | .parallel _ _ => []
  | .choice a b => headRefsList a ++ headRefsList b
  | .leftMerge _ _ => []
  | .commMerge _ _ => []
  | .restrict _ _ => []
  | .project _ _ => []
  | .ref i => [i]

theorem mem_headRefsList_iff (gp : GProc schema) (i : NodeId) :
    i ∈ headRefsList gp ↔ i ∈ headRefs gp := by
  induction gp with
  | deadlock => simp [headRefsList, headRefs]
  | nSeq N cont ih => simp only [headRefsList, headRefs]; exact ih
  | recv x N cont ih => simp [headRefsList, headRefs]
  | send x N cont ih => simp [headRefsList, headRefs]
  | rcfgPrefix x N cont ih => simp [headRefsList, headRefs]
  | parallel a b ih => simp [headRefsList, headRefs]
  | choice a b iha ihb =>
      simp only [headRefsList, headRefs, List.mem_append, Finset.mem_union]
      constructor
      · rintro (h | h)
        · exact Or.inl (iha.mp h)
        · exact Or.inr (ihb.mp h)
      · rintro (h | h)
        · exact Or.inl (iha.mpr h)
        · exact Or.inr (ihb.mpr h)
  | leftMerge a b ih => simp [headRefsList, headRefs]
  | commMerge a b ih => simp [headRefsList, headRefs]
  | restrict L cont ih => simp [headRefsList, headRefs]
  | project n cont ih => simp [headRefsList, headRefs]
  | ref i' => simp [headRefsList, headRefs]
/-- Every node returned by `headRefsList` is a `gprocRefs` member: the
    head-reference discovery only exposes references that the full
    reference set already contains, so `root_closed` and `closed` can
    be used safely through this function. -/
theorem headRefsList_subset_gprocRefs (gp : GProc schema) :
    ∀ i ∈ headRefsList gp, i ∈ gprocRefs gp := fun i hi =>
  headRefs_le_gprocRefs gp ((mem_headRefsList_iff gp i).mp hi)

------------------------------------------------------------------------
-- §2.1 Node-level head reachability
--
-- `RefReach G i j`: node `j` is reachable from node `i` by following
-- reference edges in head position (the trivial path `j = i` included).
-- This is the node-level counterpart of `HeadPathTo G (.ref i) j` and
-- is the relation the worklist invariant is stated against.
------------------------------------------------------------------------

/-- Node-level head reachability through reference edges. -/
inductive RefReach {schema : NetKAT.PacketSchema} (G : ProcessGraph schema) : NodeId → NodeId → Prop
  | refl (i : NodeId) : RefReach G i i
  | step (i v j : NodeId) (hv : v ∈ headRefs (G.label i)) (h : RefReach G v j) :
      RefReach G i j

/-- Unfolding: reachability from `i` is trivial or factors through a
    head reference of `i`'s label. -/
theorem refReach_unfold {G : ProcessGraph schema} {i j : NodeId} (h : RefReach G i j) :
    j = i ∨ ∃ v, v ∈ headRefs (G.label i) ∧ RefReach G v j := by
  cases h with
  | refl i => exact Or.inl rfl
  | step i v j hv hsub => exact Or.inr ⟨v, hv, hsub⟩

/-- A head-reachable node is either directly referenced in the head
    region or reachable through a direct head reference. -/
theorem headPathTo_refs_decomp (G : ProcessGraph schema) :
    ∀ (gp : GProc schema) (j : NodeId), HeadPathTo G gp j →
      j ∈ headRefs gp ∨ ∃ v, v ∈ headRefs gp ∧ RefReach G v j := by
  intro gp j h
  induction h with
  | ref i => exact Or.inl (by simp [headRefs])
  | nSeq N cont j _ ih =>
      rcases ih with hj | ⟨v, hv, hrv⟩
      · exact Or.inl (by simpa [headRefs] using hj)
      · exact Or.inr ⟨v, by simpa [headRefs] using hv, hrv⟩
  | choice_left a b j _ ih =>
      rcases ih with hj | ⟨v, hv, hrv⟩
      · exact Or.inl (Finset.mem_union_left _ hj)
      · exact Or.inr ⟨v, Finset.mem_union_left _ hv, hrv⟩
  | choice_right a b j _ ih =>
      rcases ih with hj | ⟨v, hv, hrv⟩
      · exact Or.inl (Finset.mem_union_right _ hj)
      · exact Or.inr ⟨v, Finset.mem_union_right _ hv, hrv⟩
  | ref_step i j _ ih =>
      refine Or.inr ⟨i, by simp [headRefs], ?_⟩
      rcases ih with hj | ⟨v, hv, hrv⟩
      · exact RefReach.step i j j hj (RefReach.refl j)
      · exact RefReach.step i v j hv hrv

/-- Inversion: term-level head reachability from a reference is the
    trivial path or factors through the node label. -/
theorem headPathTo_ref_inv {G : ProcessGraph schema} {v j : NodeId}
    (h : HeadPathTo G (.ref v) j) :
    j = v ∨ HeadPathTo G (G.label v) j := by
  cases h with
  | ref k => exact Or.inl rfl
  | ref_step _ _ h' => exact Or.inr h'

/-- Node-level and term-level head reachability from a reference
    coincide. -/
theorem refReach_iff_headPathTo (G : ProcessGraph schema) (i j : NodeId) :
    RefReach G i j ↔ HeadPathTo G (.ref i) j := by
  constructor
  · intro h
    induction h with
    | refl i => exact HeadPathTo.ref i
    | step i v j hv _ ih =>
        refine HeadPathTo.ref_step i j ?_
        rcases headPathTo_ref_inv ih with hj | h'
        · subst hj
          exact headRefs_pathTo G (G.label i) _ hv
        · exact headPathTo_trans (headRefs_pathTo G (G.label i) v hv) h'
  · intro h
    cases h with
    | ref i => exact RefReach.refl i
    | ref_step i j hsub =>
        rcases headPathTo_refs_decomp G (G.label i) j hsub with hj | ⟨v, hv, hrv⟩
        · exact RefReach.step i j j hj (RefReach.refl j)
        · exact RefReach.step i v j hv hrv

/-- Every head-reachable node of a graph whose root references and node
    labels are closed lives in the node set: this is where
    `headRefs_le_gprocRefs` makes `root_closed` and `closed` usable. -/
theorem headPathTo_nodes (G : ProcessGraph schema) :
    ∀ (gp : GProc schema) (j : NodeId), HeadPathTo G gp j →
      (∀ i, i ∈ headRefs gp → i ∈ G.nodes) →
      (∀ i ∈ G.nodes, ∀ k, k ∈ headRefs (G.label i) → k ∈ G.nodes) →
      j ∈ G.nodes := by
  intro gp j h
  induction h with
  | ref i => intro hrefs _; exact hrefs i (by simp [headRefs])
  | nSeq N cont k _ ih =>
      intro hrefs hcl
      exact ih (fun i hi => hrefs i (by simpa [headRefs] using hi)) hcl
  | choice_left a b k _ ih =>
      intro hrefs hcl
      exact ih (fun i hi => hrefs i (Finset.mem_union_left _ hi)) hcl
  | choice_right a b k _ ih =>
      intro hrefs hcl
      exact ih (fun i hi => hrefs i (Finset.mem_union_right _ hi)) hcl
  | ref_step i k _ ih =>
      intro hrefs hcl
      exact ih (hcl i (hrefs i (by simp [headRefs]))) hcl

/-- For the root of a well-formed graph, head-reachable nodes are live:
    the two closure hypotheses are exactly `root_closed` and `closed`,
    connected through `headRefs_le_gprocRefs`. -/
theorem headPathTo_nodes_closed (G : ProcessGraph schema) (j : NodeId)
    (h : HeadPathTo G G.root j) : j ∈ G.nodes :=
  headPathTo_nodes G G.root j h
    (fun _i hi => G.root_closed (headRefs_le_gprocRefs G.root hi))
    (fun i hi _k hk => G.closed i hi (headRefs_le_gprocRefs (G.label i) hk))


------------------------------------------------------------------------
-- §2.2 The cycle-safe worklist
--
-- `headRun G pending visited acc` processes the pending worklist: a
-- visited node is skipped, an unvisited node is validated against
-- `G.nodes` (a reference outside the graph fails explicitly), then
-- visited, recorded in `acc`, and its label's head references are
-- appended to the worklist.  Termination is by the lexicographic
-- measure ((G.nodes \ visited).card, pending.length): visiting a fresh
-- node of `G.nodes` strictly decreases the number of unvisited graph
-- nodes, and skipping a pending node strictly shortens the worklist.
------------------------------------------------------------------------

/-- The cycle-safe head worklist.  Returns the list of visited nodes in
    visit order, or `none` when a pending reference lies outside
    `G.nodes`. -/
def headRun (G : ProcessGraph schema) :
    List NodeId → Finset NodeId → List NodeId → Option (List NodeId)
  | [], _, acc => some acc
  | i :: rest, visited, acc =>
      if _h : i ∈ visited then headRun G rest visited acc
      else if _h2 : i ∈ G.nodes then
        headRun G (rest ++ headRefsList (G.label i)) (insert i visited) (i :: acc)
      else none
termination_by pending visited _ => ((G.nodes \ visited).card, pending.length)
decreasing_by
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  · have hsdiff : G.nodes \ insert i visited = (G.nodes \ visited).erase i := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      tauto
    have himem : i ∈ (G.nodes \ visited) := by
      simp only [Finset.mem_sdiff]
      exact ⟨_h2, _h⟩
    have hcard : (G.nodes \ insert i visited).card = (G.nodes \ visited).card - 1 := by
      rw [hsdiff, Finset.card_erase_of_mem himem]
    have hpos : 0 < (G.nodes \ visited).card := (Finset.card_pos).mpr ⟨i, himem⟩
    have hlt : (G.nodes \ insert i visited).card < (G.nodes \ visited).card := by omega
    exact Prod.Lex.left _ _ hlt

/-- Worklist coverage through already-visited nodes: if everything
    reachable from a visited node must still be found, the worklist
    frontier contains a witness outside the visited set. -/
theorem headRun_cover_visited (G : ProcessGraph schema) (visited : Finset NodeId)
    (pending : List NodeId)
    (hF : ∀ i₀ ∈ visited, ∀ v, v ∈ headRefs (G.label i₀) → v ∈ visited ∨ v ∈ pending)
    (i₀ j : NodeId) (h : RefReach G i₀ j) :
    i₀ ∈ visited → j ∉ visited →
      ∃ i', i' ∈ pending ∧ i' ∉ visited ∧ RefReach G i' j := by
  induction h with
  | refl i =>
      intro hmem hnot
      exact absurd hmem hnot
  | step i v j hv hsub ih =>
      intro hmem hnot
      rcases hF i hmem v hv with hv' | hv'
      · exact ih hv' hnot
      · by_cases hvv : v ∈ visited
        · exact ih hvv hnot
        · exact ⟨v, hv', hvv, hsub⟩

/-- The full worklist invariant: pending nodes are head-reachable,
    every head-reachable node is visited or reachable from a pending
    node, visited nodes have had their head references accounted for,
    and the accumulator records exactly the visited nodes. -/
theorem headRun_spec (G : ProcessGraph schema) (pending : List NodeId)
    (visited : Finset NodeId) (acc : List NodeId)
    (hB : ∀ i ∈ acc, HeadPathTo G G.root i ∧ i ∈ G.nodes)
    (hC : ∀ i ∈ visited, i ∈ acc)
    (hD : ∀ i ∈ pending, HeadPathTo G G.root i)
    (hE : ∀ j, HeadPathTo G G.root j → j ∈ visited ∨ ∃ i, i ∈ pending ∧ RefReach G i j)
    (hF : ∀ i₀ ∈ visited, ∀ v, v ∈ headRefs (G.label i₀) → v ∈ visited ∨ v ∈ pending) :
    (headRun G pending visited acc = none →
        ∃ j, HeadPathTo G G.root j ∧ j ∉ G.nodes) ∧
      (∀ L, headRun G pending visited acc = some L →
        (∀ j, HeadPathTo G G.root j → j ∈ L) ∧
          ∀ j ∈ L, HeadPathTo G G.root j ∧ j ∈ G.nodes) := by
  fun_induction headRun G pending visited acc
  case case1 visited acc =>
    refine ⟨fun h => ?_, fun L hL => ?_⟩
    · rw [headRun.eq_1] at h
      exact Option.noConfusion h
    · rw [headRun.eq_1] at hL
      have hacc : acc = L := Option.some.inj hL
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · rcases hE j hj with hj' | ⟨k, hk, _⟩
        · have hjacc : j ∈ acc := hC j hj'
          rw [hacc] at hjacc
          exact hjacc
        · simp at hk
      · have hjacc : j ∈ acc := by rw [hacc]; exact hj
        exact hB j hjacc
  case case2 i rest visited acc h ih =>
    have heq : headRun G (i :: rest) visited acc = headRun G rest visited acc := by
      rw [headRun.eq_2, dif_pos h]
    have hD' : ∀ k ∈ rest, HeadPathTo G G.root k := fun k hk =>
      hD k (List.mem_cons_of_mem _ hk)
    have hF' : ∀ i₀ ∈ visited, ∀ v, v ∈ headRefs (G.label i₀) →
        v ∈ visited ∨ v ∈ rest := by
      intro i₀ hi₀ v hv
      rcases hF i₀ hi₀ v hv with hv' | hv'
      · exact Or.inl hv'
      · rcases List.mem_cons.mp hv' with hvEq | hv''
        · rw [hvEq]
          exact Or.inl h
        · exact Or.inr hv''
    have hE' : ∀ j, HeadPathTo G G.root j →
        j ∈ visited ∨ ∃ k, k ∈ rest ∧ RefReach G k j := by
      intro j hj
      rcases hE j hj with hj' | ⟨k, hk, hrk⟩
      · exact Or.inl hj'
      · rcases List.mem_cons.mp hk with hkEq | hk'
        · simp only [hkEq] at hrk
          by_cases hjv : j ∈ visited
          · exact Or.inl hjv
          · obtain ⟨i', hi', hi'v, hi'r⟩ :=
              headRun_cover_visited G visited (i :: rest) hF i j hrk h hjv
            rcases List.mem_cons.mp hi' with hiEq | hi''
            · rw [hiEq] at hi'v
              exact absurd h hi'v
            · exact Or.inr ⟨i', hi'', hi'r⟩
        · exact Or.inr ⟨k, hk', hrk⟩
    refine ⟨fun hnone => ?_, fun L hL => ?_⟩
    · rw [heq] at hnone
      exact (ih hB hC hD' hE' hF').1 hnone
    · rw [heq] at hL
      exact (ih hB hC hD' hE' hF').2 L hL
  case case3 i rest visited acc h1 h2 ih =>
    have heq : headRun G (i :: rest) visited acc =
        headRun G (rest ++ headRefsList (G.label i)) (insert i visited) (i :: acc) := by
      rw [headRun.eq_2, dif_neg h1, dif_pos h2]
    have hB' : ∀ k ∈ i :: acc, HeadPathTo G G.root k ∧ k ∈ G.nodes := by
      intro k hk
      rcases List.mem_cons.mp hk with hkEq | hk'
      · rw [hkEq]
        exact ⟨hD i (List.Mem.head _), h2⟩
      · exact hB k hk'
    have hC' : ∀ k ∈ insert i visited, k ∈ i :: acc := by
      intro k hk
      rcases Finset.mem_insert.mp hk with hkEq | hk'
      · rw [hkEq]
        exact List.Mem.head _
      · exact List.Mem.tail _ (hC k hk')
    have hD' : ∀ k ∈ rest ++ headRefsList (G.label i), HeadPathTo G G.root k := by
      intro k hk
      rcases List.mem_append.mp hk with hk' | hk'
      · exact hD k (List.mem_cons_of_mem _ hk')
      · have hkR : k ∈ headRefs (G.label i) :=
          (mem_headRefsList_iff (G.label i) k).mp hk'
        exact headPathTo_trans (hD i (List.Mem.head _))
          (headRefs_pathTo G (G.label i) k hkR)
    have hE' : ∀ j, HeadPathTo G G.root j →
        j ∈ insert i visited ∨ ∃ k, k ∈ rest ++ headRefsList (G.label i) ∧ RefReach G k j := by
      intro j hj
      rcases hE j hj with hj' | ⟨k, hk, hrk⟩
      · exact Or.inl (Finset.mem_insert_of_mem hj')
      · rcases List.mem_cons.mp hk with hkEq | hk'
        · simp only [hkEq] at hrk
          rcases refReach_unfold hrk with hj2 | ⟨v, hv, hrv⟩
          · rw [hj2]
            exact Or.inl (Finset.mem_insert_self i visited)
          · exact Or.inr ⟨v, List.mem_append_right _
              ((mem_headRefsList_iff (G.label i) v).mpr hv), hrv⟩
        · exact Or.inr ⟨k, List.mem_append_left _ hk', hrk⟩
    have hF' : ∀ i₀ ∈ insert i visited, ∀ v, v ∈ headRefs (G.label i₀) →
        v ∈ insert i visited ∨ v ∈ rest ++ headRefsList (G.label i) := by
      intro i₀ hi₀ v hv
      rcases Finset.mem_insert.mp hi₀ with hiEq | hi₀'
      · rw [hiEq] at hv
        exact Or.inr (List.mem_append_right _
          ((mem_headRefsList_iff (G.label i) v).mpr hv))
      · rcases hF i₀ hi₀' v hv with hv' | hv'
        · exact Or.inl (Finset.mem_insert_of_mem hv')
        · rcases List.mem_cons.mp hv' with hvEq | hv''
          · rw [hvEq]
            exact Or.inl (Finset.mem_insert_self i visited)
          · exact Or.inr (List.mem_append_left _ hv'')
    refine ⟨fun hnone => ?_, fun L hL => ?_⟩
    · rw [heq] at hnone
      exact (ih hB' hC' hD' hE' hF').1 hnone
    · rw [heq] at hL
      exact (ih hB' hC' hD' hE' hF').2 L hL
  case case4 i rest visited acc h1 h2 =>
    refine ⟨fun _ => ⟨i, hD i (List.Mem.head _), h2⟩, fun L hL => ?_⟩
    rw [headRun.eq_2, dif_neg h1, dif_neg h2] at hL
    exact Option.noConfusion hL

/-- Worklist failure for the graph root: if the traversal from
    `headRefsList G.root` fails, some head-reachable node is not a node
    of the graph. -/
theorem headRun_root_failure (G : ProcessGraph schema)
    (h : headRun G (headRefsList G.root) ∅ [] = none) :
    ∃ j, HeadPathTo G G.root j ∧ j ∉ G.nodes := by
  have hE : ∀ j, HeadPathTo G G.root j →
      j ∈ (∅ : Finset NodeId) ∨ ∃ i, i ∈ headRefsList G.root ∧ RefReach G i j :=
    fun j hj => Or.inr (by
      rcases headPathTo_refs_decomp G G.root j hj with hj' | ⟨v, hv, hrv⟩
      · exact ⟨j, (mem_headRefsList_iff G.root j).mpr hj', RefReach.refl j⟩
      · exact ⟨v, (mem_headRefsList_iff G.root v).mpr hv, hrv⟩)
  exact (headRun_spec G (headRefsList G.root) ∅ []
    (by intro i hi; simp at hi)
    (by intro i hi; exact absurd hi (Finset.not_mem_empty i))
    (fun i hi => headRefs_pathTo G G.root i ((mem_headRefsList_iff G.root i).mp hi))
    hE
    (by intro i₀ hi; exact absurd hi (Finset.not_mem_empty i₀))).1 h

/-- Worklist success for the graph root: if the traversal succeeds with
    `L`, then `L` contains EXACTLY the head-reachable nodes of `G.root`,
    and all of them are live nodes of the graph. -/
theorem headRun_root_success (G : ProcessGraph schema) (L : List NodeId)
    (h : headRun G (headRefsList G.root) ∅ [] = some L) :
    (∀ j, HeadPathTo G G.root j → j ∈ L) ∧
      ∀ j ∈ L, HeadPathTo G G.root j ∧ j ∈ G.nodes := by
  have hE : ∀ j, HeadPathTo G G.root j →
      j ∈ (∅ : Finset NodeId) ∨ ∃ i, i ∈ headRefsList G.root ∧ RefReach G i j :=
    fun j hj => Or.inr (by
      rcases headPathTo_refs_decomp G G.root j hj with hj' | ⟨v, hv, hrv⟩
      · exact ⟨j, (mem_headRefsList_iff G.root j).mpr hj', RefReach.refl j⟩
      · exact ⟨v, (mem_headRefsList_iff G.root v).mpr hv, hrv⟩)
  exact (headRun_spec G (headRefsList G.root) ∅ []
    (by intro i hi; simp at hi)
    (by intro i hi; exact absurd hi (Finset.not_mem_empty i))
    (fun i hi => headRefs_pathTo G G.root i ((mem_headRefsList_iff G.root i).mp hi))
    hE
    (by intro i₀ hi; exact absurd hi (Finset.not_mem_empty i₀))).2 L h

------------------------------------------------------------------------
-- §3 Local policy collection
--
-- `headCollect gp` unions the NetKAT policies of the packet prefixes in
-- the head region of `gp`, following the paper's equations (29)-(31):
-- deadlock and reconfiguration prefixes contribute `.drop` (Eqs. 29
-- and 32), a packet prefix contributes its policy and its continuation
-- is traversed (Eq. 30), and choice unions both branches (Eq. 31).  A
-- reference `ref i` contributes `.drop` LOCALLY: its node label is
-- collected separately by the worklist, so collection never follows
-- graph references and repeated references cannot cause repeated
-- traversal.  Unsupported constructors (`recv`, `send`, `parallel`,
-- `leftMerge`, `commMerge`, `restrict`, `project`) fail explicitly,
-- never silently as zero.
--
-- The traversal is STRUCTURALLY recursive and executable.
------------------------------------------------------------------------

/-- Local head-policy collection of a graph term. -/
def headCollect : GProc schema → Option (NetKAT schema)
  | .deadlock => some .drop
  | .nSeq N cont => (headCollect cont).map (fun H => NetKAT.union N H)
  | .recv _ _ _ => none
  | .send _ _ _ => none
  | .rcfgPrefix _ _ _ => some .drop
  | .parallel _ _ => none
  | .choice a b =>
      (headCollect a).bind
        (fun H₁ => (headCollect b).map (fun H₂ => NetKAT.union H₁ H₂))
  | .leftMerge _ _ => none
  | .commMerge _ _ => none
  | .restrict _ _ => none
  | .project _ _ => none
  | .ref _ => some .drop

/-- Defining equations of `headCollect` (paper Eqs. (29)-(32)). -/
theorem headCollect_deadlock : headCollect (schema := schema) .deadlock = some .drop := rfl

theorem headCollect_nSeq (N : NetKAT schema) (cont : GProc schema) :
    headCollect (.nSeq N cont) =
      (headCollect cont).map (fun H => NetKAT.union N H) := rfl

theorem headCollect_choice (a b : GProc schema) :
    headCollect (.choice a b) =
      (headCollect a).bind
        (fun H₁ => (headCollect b).map (fun H₂ => NetKAT.union H₁ H₂)) := rfl

theorem headCollect_rcfgPrefix (x : Channel) (N : NetKAT schema) (cont : GProc schema) :
    headCollect (.rcfgPrefix x N cont) = some .drop := rfl

theorem headCollect_recv (x : Channel) (N : NetKAT schema) (cont : GProc schema) :
    headCollect (.recv x N cont) = none := rfl

theorem headCollect_send (x : Channel) (N : NetKAT schema) (cont : GProc schema) :
    headCollect (.send x N cont) = none := rfl

theorem headCollect_parallel (a b : GProc schema) :
    headCollect (.parallel a b) = none := rfl

theorem headCollect_leftMerge (a b : GProc schema) :
    headCollect (.leftMerge a b) = none := rfl

theorem headCollect_commMerge (a b : GProc schema) :
    headCollect (.commMerge a b) = none := rfl

theorem headCollect_restrict (L : Set (CommunicationAction schema)) (cont : GProc schema) :
    headCollect (.restrict L cont) = none := rfl

theorem headCollect_project (n : Nat) (cont : GProc schema) :
    headCollect (.project n cont) = none := rfl

theorem headCollect_ref (i : NodeId) : headCollect (schema := schema) (.ref i) = some .drop := rfl

/-- Eq. (30) in the paper's shape: a successful continuation extraction
    gives `N + H`. -/
theorem headCollect_nSeq_eq (N : NetKAT schema) (cont : GProc schema) (H : NetKAT schema)
    (h : headCollect cont = some H) :
    headCollect (.nSeq N cont) = some (NetKAT.union N H) := by
  rw [headCollect_nSeq, h]
  rfl

/-- Eq. (31) in the paper's shape. -/
theorem headCollect_choice_eq (a b : GProc schema) (H₁ H₂ : NetKAT schema)
    (ha : headCollect a = some H₁) (hb : headCollect b = some H₂) :
    headCollect (.choice a b) = some (NetKAT.union H₁ H₂) := by
  rw [headCollect_choice, ha, hb]
  rfl

/-- Failure propagation through `N;D`. -/
theorem headCollect_nSeq_none (N : NetKAT schema) (cont : GProc schema)
    (h : headCollect cont = none) : headCollect (.nSeq N cont) = none := by
  rw [headCollect_nSeq, h]
  rfl

/-- Failure propagation through `D ⊕ Q` from the left branch. -/
theorem headCollect_choice_none_left (a b : GProc schema)
    (h : headCollect a = none) : headCollect (.choice a b) = none := by
  rw [headCollect_choice, h]
  rfl

/-- Failure propagation through `D ⊕ Q` from the right branch. -/
theorem headCollect_choice_none_right (a b : GProc schema)
    (h : headCollect b = none) : headCollect (.choice a b) = none := by
  cases ha : headCollect a with
  | none => rw [headCollect_choice, ha]; rfl
  | some H₁ => rw [headCollect_choice, ha, h]; rfl

/-- Inversion for Eq. (30): a successful extraction from `N; cont`
    determines a successful extraction of the continuation. -/
theorem headCollect_nSeq_inv (N : NetKAT schema) (cont : GProc schema) (H : NetKAT schema)
    (h : headCollect (.nSeq N cont) = some H) :
    ∃ H', headCollect cont = some H' ∧ H = NetKAT.union N H' := by
  rw [headCollect_nSeq, Option.map_eq_some'] at h
  obtain ⟨H', h', hH⟩ := h
  exact ⟨H', h', hH.symm⟩

/-- Inversion for Eq. (31): a successful extraction from `D ⊕ Q`
    determines successful extractions of both branches. -/
theorem headCollect_choice_inv (a b : GProc schema) (H : NetKAT schema)
    (h : headCollect (.choice a b) = some H) :
    ∃ H₁ H₂ : NetKAT schema, headCollect a = some H₁ ∧ headCollect b = some H₂ ∧
      H = NetKAT.union H₁ H₂ := by
  rw [headCollect_choice, Option.bind_eq_some] at h
  obtain ⟨H₁, ha, hmap⟩ := h
  rw [Option.map_eq_some'] at hmap
  obtain ⟨H₂, hb, hH⟩ := hmap
  exact ⟨H₁, H₂, ha, hb, hH.symm⟩

/-- The collection succeeds on every ref-free head-subterm of a
    successful term. -/
theorem headCollect_subSuccess (G : ProcessGraph schema) :
    ∀ {gp sub : GProc schema}, HeadSubFree G gp sub →
      ∀ H : NetKAT schema, headCollect gp = some H →
        ∃ H', headCollect sub = some H' := by
  intro gp sub hs
  induction hs with
  | refl gp => intro H h; exact ⟨H, h⟩
  | nSeq N cont sub _ ih =>
      intro H h
      obtain ⟨H', h', _⟩ := headCollect_nSeq_inv N cont H h
      exact ih H' h'
  | choice_left a b sub _ ih =>
      intro H h
      obtain ⟨H₁, H₂, ha, hb, _⟩ := headCollect_choice_inv a b H h
      exact ih H₁ ha
  | choice_right a b sub _ ih =>
      intro H h
      obtain ⟨H₁, H₂, ha, hb, _⟩ := headCollect_choice_inv a b H h
      exact ih H₂ hb

/-- The collection of a containing term covers the semantics of the
    collection of each of its ref-free head-subterms: the containing
    term's union tree includes the subterm's union tree. -/
theorem headCollect_subCover (G : ProcessGraph schema) (σ τ : schema.Packet) :
    ∀ {ct gp : GProc schema}, HeadSubFree G ct gp →
      ∀ Hct Hgp : NetKAT schema, headCollect ct = some Hct →
        headCollect gp = some Hgp → Semantics Hgp σ τ → Semantics Hct σ τ := by
  intro ct gp hs
  induction hs with
  | refl gp =>
      intro Hct Hgp hct hgp hsem
      have heq : Hct = Hgp := Option.some.inj (hct.symm.trans hgp)
      subst heq
      exact hsem
  | nSeq N cont sub _ ih =>
      intro Hct Hgp hct hgp hsem
      obtain ⟨H', h', hHct⟩ := headCollect_nSeq_inv N cont Hct hct
      subst hHct
      exact (union_sem N H' σ τ).mpr (Or.inr (ih H' Hgp h' hgp hsem))
  | choice_left a b sub _ ih =>
      intro Hct Hgp hct hgp hsem
      obtain ⟨H₁, H₂, ha, hb, hHct⟩ := headCollect_choice_inv a b Hct hct
      subst hHct
      exact (union_sem H₁ H₂ σ τ).mpr (Or.inl (ih H₁ Hgp ha hgp hsem))
  | choice_right a b sub _ ih =>
      intro Hct Hgp hct hgp hsem
      obtain ⟨H₁, H₂, ha, hb, hHct⟩ := headCollect_choice_inv a b Hct hct
      subst hHct
      exact (union_sem H₁ H₂ σ τ).mpr (Or.inr (ih H₂ Hgp hb hgp hsem))

------------------------------------------------------------------------
-- §4 Combining traversal and collection
--
-- `graphHead G` unions the head-policy collection of the root term
-- with the head-policy collection of the label of every node the
-- worklist visits.  The union is computed by a list fold with sticky
-- failure: the first failed component makes the whole extraction fail
-- explicitly, so an unsupported reachable shape is never silently
-- treated as the zero policy.
------------------------------------------------------------------------

/-- One union step: add the contribution of node `j` to the accumulator. -/
def unionStep (f : NodeId → Option (NetKAT schema)) (j : NodeId) (acc : Option (NetKAT schema)) :
    Option (NetKAT schema) :=
  (f j).bind fun H => acc.map fun acc' => NetKAT.union acc' H

/-- The union over a list of node contributions. -/
def unionOverList (f : NodeId → Option (NetKAT schema)) :
    List NodeId → Option (NetKAT schema) → Option (NetKAT schema)
  | [], acc => acc
  | j :: js, acc => unionOverList f js (unionStep f j acc)

theorem unionStep_eq_some (f : NodeId → Option (NetKAT schema)) (j : NodeId)
    (acc : Option (NetKAT schema)) (H₁ acc' : NetKAT schema)
    (hfj : f j = some H₁) (hacc : acc = some acc') :
    unionStep f j acc = some (NetKAT.union acc' H₁) := by
  rw [unionStep, hfj, hacc]
  rfl

theorem unionStep_inv (f : NodeId → Option (NetKAT schema)) (j : NodeId)
    (acc : Option (NetKAT schema)) (X : NetKAT schema) (h : unionStep f j acc = some X) :
    ∃ H₁ acc' : NetKAT schema, f j = some H₁ ∧ acc = some acc' ∧
      X = NetKAT.union acc' H₁ := by
  rw [unionStep, Option.bind_eq_some] at h
  obtain ⟨H₁, hfj, hmap⟩ := h
  rw [Option.map_eq_some'] at hmap
  obtain ⟨acc', hacc, hX⟩ := hmap
  exact ⟨H₁, acc', hfj, hacc, hX.symm⟩

theorem unionStep_none_inv (f : NodeId → Option (NetKAT schema)) (j : NodeId)
    (acc : Option (NetKAT schema)) (h : unionStep f j acc = none) :
    f j = none ∨ acc = none := by
  by_cases hfj : f j = none
  · exact Or.inl hfj
  · obtain ⟨H₁, hfj'⟩ := Option.ne_none_iff_exists.mp hfj
    rw [unionStep, ← hfj'] at h
    simp at h
    exact Or.inr h

theorem unionOverList_none (f : NodeId → Option (NetKAT schema)) :
    ∀ l : List NodeId, unionOverList f l none = none := by
  intro l
  induction l with
  | nil => rfl
  | cons j js ih =>
      rw [unionOverList, unionStep]
      cases hfj : f j with
      | none => simp [ih]
      | some H => simp [ih]

/-- Inversion for the cons step of a successful union. -/
theorem unionOverList_cons_inv (f : NodeId → Option (NetKAT schema)) (j : NodeId)
    (js : List NodeId) (start : Option (NetKAT schema)) (H : NetKAT schema)
    (h : unionOverList f (j :: js) start = some H) :
    ∃ H₁ acc' : NetKAT schema, f j = some H₁ ∧ start = some acc' ∧
      unionOverList f js (some (NetKAT.union acc' H₁)) = some H := by
  rw [unionOverList] at h
  cases hstep : unionStep f j start with
  | none =>
      rw [hstep] at h
      rw [unionOverList_none f js] at h
      exact Option.noConfusion h
  | some X =>
      rw [hstep] at h
      obtain ⟨H₁, acc', hfj, hacc, hX⟩ := unionStep_inv f j start X hstep
      subst hacc
      rw [hX] at h
      exact ⟨H₁, acc', hfj, rfl, h⟩

theorem unionOverList_none_inv (f : NodeId → Option (NetKAT schema)) :
    ∀ (l : List NodeId) (start : Option (NetKAT schema)),
      unionOverList f l start = none →
      start = none ∨ ∃ j, j ∈ l ∧ f j = none := by
  intro l
  induction l with
  | nil => intro start h; exact Or.inl h
  | cons j js ih =>
      intro start h
      rw [unionOverList] at h
      cases hstep : unionStep f j start with
      | none =>
          rcases unionStep_none_inv f j start hstep with hfj | hacc
          · exact Or.inr ⟨j, List.Mem.head _, hfj⟩
          · exact Or.inl hacc
      | some X =>
          rw [hstep] at h
          rcases ih _ h with hfalse | ⟨j', hj', hf⟩
          · exact absurd hfalse (by simp)
          · exact Or.inr ⟨j', List.Mem.tail _ hj', hf⟩

theorem unionOverList_all_some (f : NodeId → Option (NetKAT schema)) :
    ∀ (l : List NodeId) (H₀ H : NetKAT schema),
      unionOverList f l (some H₀) = some H →
      ∀ j, j ∈ l → ∃ Hⱼ, f j = some Hⱼ := by
  intro l
  induction l with
  | nil => intro H₀ H h j hj; exact absurd hj (by simp)
  | cons j js ih =>
      intro H₀ H h x hx
      obtain ⟨H₁, acc', hfj, hacc, hrest⟩ := unionOverList_cons_inv f j js (some H₀) H h
      have hacc' : H₀ = acc' := Option.some.inj hacc
      subst hacc'
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨H₁, hfj⟩
      · exact ih _ _ hrest x hx'

theorem unionOverList_start_cover (f : NodeId → Option (NetKAT schema)) (σ τ : schema.Packet) :
    ∀ (l : List NodeId) (H₀ H : NetKAT schema),
      unionOverList f l (some H₀) = some H →
      Semantics H₀ σ τ → Semantics H σ τ := by
  intro l
  induction l with
  | nil =>
      intro H₀ H h hsem
      have hH : H₀ = H := Option.some.inj h
      subst hH
      exact hsem
  | cons j js ih =>
      intro H₀ H h hsem
      obtain ⟨H₁, acc', hfj, hacc, hrest⟩ := unionOverList_cons_inv f j js (some H₀) H h
      have hacc' : H₀ = acc' := Option.some.inj hacc
      subst hacc'
      exact ih _ _ hrest ((union_sem H₀ H₁ σ τ).mpr (Or.inl hsem))

theorem unionOverList_mem_cover (f : NodeId → Option (NetKAT schema)) (σ τ : schema.Packet) :
    ∀ (l : List NodeId) (H₀ H : NetKAT schema),
      unionOverList f l (some H₀) = some H →
      ∀ j, j ∈ l → ∀ Hⱼ : NetKAT schema, f j = some Hⱼ → Semantics Hⱼ σ τ →
        Semantics H σ τ := by
  intro l
  induction l with
  | nil => intro H₀ H h j hj; exact absurd hj (by simp)
  | cons j' js ih =>
      intro H₀ H h j hj Hⱼ hfj hsem
      obtain ⟨H₁, acc', hfj', hacc, hrest⟩ :=
        unionOverList_cons_inv f j' js (some H₀) H h
      have hacc' : H₀ = acc' := Option.some.inj hacc
      subst hacc'
      rcases List.mem_cons.mp hj with rfl | hj'
      · have hHeq : H₁ = Hⱼ := (Option.some.inj (hfj.symm.trans hfj')).symm
        subst hHeq
        exact unionOverList_start_cover f σ τ js _ H hrest
          ((union_sem H₀ H₁ σ τ).mpr (Or.inr hsem))
      · exact ih _ _ hrest j hj' Hⱼ hfj hsem

theorem unionOverList_sem_decomp (f : NodeId → Option (NetKAT schema)) (σ τ : schema.Packet) :
    ∀ (l : List NodeId) (H₀ H : NetKAT schema),
      unionOverList f l (some H₀) = some H →
      Semantics H σ τ →
      Semantics H₀ σ τ ∨
        (∃ j, j ∈ l ∧ ∃ Hⱼ, f j = some Hⱼ ∧ Semantics Hⱼ σ τ) := by
  intro l
  induction l with
  | nil =>
      intro H₀ H h hsem
      have hH : H₀ = H := Option.some.inj h
      subst hH
      exact Or.inl hsem
  | cons j js ih =>
      intro H₀ H h hsem
      obtain ⟨H₁, acc', hfj, hacc, hrest⟩ := unionOverList_cons_inv f j js (some H₀) H h
      have hacc' : H₀ = acc' := Option.some.inj hacc
      subst hacc'
      rcases ih _ _ hrest hsem with hacc'' | ⟨j', hj', Hⱼ', hfj', hsem'⟩
      · rcases (union_sem H₀ H₁ σ τ).mp hacc'' with h₀ | h₁
        · exact Or.inl h₀
        · exact Or.inr ⟨j, List.Mem.head _, H₁, hfj, h₁⟩
      · exact Or.inr ⟨j', List.Mem.tail _ hj', Hⱼ', hfj', hsem'⟩

/-- Success of the union fold over a fully-collected node list. -/
theorem unionOverList_some (f : NodeId → Option (NetKAT schema)) :
    ∀ (l : List NodeId) (start : Option (NetKAT schema)) (H₀ : NetKAT schema),
      start = some H₀ → (∀ j, j ∈ l → ∃ Hⱼ, f j = some Hⱼ) →
      ∃ H, unionOverList f l start = some H := by
  intro l
  induction l with
  | nil => intro start H₀ hs _; exact ⟨H₀, hs⟩
  | cons j js ih =>
      intro start H₀ hs hall
      obtain ⟨Hⱼ, hfj⟩ := hall j (List.Mem.head _)
      have hstep : unionStep f j start = some (NetKAT.union H₀ Hⱼ) := by
        rw [unionStep, hfj, hs]
        rfl
      rw [unionOverList, hstep]
      exact ih _ (NetKAT.union H₀ Hⱼ) rfl (fun k hk => hall k (List.Mem.tail _ hk))

/-- The union of the root contribution with the contribution of every
    visited node's label.  The fold runs over the worklist's visited
    list, so the extraction is executable. -/
def graphHeadUnion (G : ProcessGraph schema) (L : List NodeId)
    (start : Option (NetKAT schema)) : Option (NetKAT schema) :=
  unionOverList (fun j => headCollect (G.label j)) L start

/-- **Graph-native head extraction**: the head policy of the graph `G`,
    computed from the finite graph without unfolding recursive
    definitions.  The root is `G.root`, so the graph's `root_closed`
    guarantee applies. -/
def graphHead (G : ProcessGraph schema) : Option (NetKAT schema) :=
  match headRun G (headRefsList G.root) ∅ [] with
  | none => none
  | some L => graphHeadUnion G L (headCollect G.root)

------------------------------------------------------------------------
-- §5 The independent relational specification
------------------------------------------------------------------------

/-- Independent relational specification of graph-native `head`
    extraction (paper Eqs. (29)-(32) lifted to the graph).

    `GraphHeadSpec G gp σ τ` holds exactly when the packet pair `(σ, τ)`
    is contributed by a NetKAT policy occurring at a packet-processing
    prefix reachable from `gp` before any reconfiguration boundary:

      GraphHeadSpec ⊥ (σ,τ)          = false                     (Eq. 29)
      GraphHeadSpec (N;D) (σ,τ)      = ⟦N⟧(σ,τ) ∨ spec(D)        (Eq. 30)
      GraphHeadSpec (D⊕Q) (σ,τ)      = spec(D) ∨ spec(Q)         (Eq. 31)
      GraphHeadSpec (rcfg_{x,N};D)   = false                     (Eq. 32)
      GraphHeadSpec (ref i) (σ,τ)    = spec(G.label i)

    Recursive references follow their graph edges; recursive cycles are
    represented by finite derivations of the least-fixpoint relation,
    never by infinite unfolding.  The relation never mentions
    `graphHead`, so the correctness theorem is meaningful. -/
inductive GraphHeadSpec {schema : NetKAT.PacketSchema} (G : ProcessGraph schema) : GProc schema → schema.Packet → schema.Packet → Prop
  | nSeq_of_sem (N : NetKAT schema) (cont : GProc schema) (σ τ : schema.Packet)
      (h : Semantics N σ τ) : GraphHeadSpec G (.nSeq N cont) σ τ
  | nSeq_of_tail (N : NetKAT schema) (cont : GProc schema) (σ τ : schema.Packet)
      (h : GraphHeadSpec G cont σ τ) : GraphHeadSpec G (.nSeq N cont) σ τ
  | choice_left (a b : GProc schema) (σ τ : schema.Packet)
      (h : GraphHeadSpec G a σ τ) : GraphHeadSpec G (.choice a b) σ τ
  | choice_right (a b : GProc schema) (σ τ : schema.Packet)
      (h : GraphHeadSpec G b σ τ) : GraphHeadSpec G (.choice a b) σ τ
  | ref_of (i : NodeId) (σ τ : schema.Packet)
      (h : GraphHeadSpec G (G.label i) σ τ) : GraphHeadSpec G (.ref i) σ τ

/-- Spec clause for Eq. (29): ⊥ contributes the empty relation. -/
theorem graphHeadSpec_deadlock_false (G : ProcessGraph schema) (σ τ : schema.Packet) :
    ¬ GraphHeadSpec G .deadlock σ τ := by
  intro h
  cases h

/-- Spec clause for Eq. (32): a reconfiguration prefix contributes the
    empty relation. -/
theorem graphHeadSpec_rcfgPrefix_false (G : ProcessGraph schema) (x : Channel)
    (N : NetKAT schema) (cont : GProc schema) (σ τ : schema.Packet) :
    ¬ GraphHeadSpec G (.rcfgPrefix x N cont) σ τ := by
  intro h
  cases h

/-- Spec clause for Eq. (30). -/
theorem graphHeadSpec_nSeq_iff (G : ProcessGraph schema) (N : NetKAT schema) (cont : GProc schema)
    (σ τ : schema.Packet) :
    GraphHeadSpec G (.nSeq N cont) σ τ ↔
      (Semantics N σ τ ∨ GraphHeadSpec G cont σ τ) := by
  constructor
  · intro h
    cases h with
    | nSeq_of_sem _ _ _ _ hsem => exact Or.inl hsem
    | nSeq_of_tail _ _ _ _ ht => exact Or.inr ht
  · intro h
    rcases h with hsem | ht
    · exact GraphHeadSpec.nSeq_of_sem N cont σ τ hsem
    · exact GraphHeadSpec.nSeq_of_tail N cont σ τ ht

/-- Spec clause for Eq. (31). -/
theorem graphHeadSpec_choice_iff (G : ProcessGraph schema) (a b : GProc schema) (σ τ : schema.Packet) :
    GraphHeadSpec G (.choice a b) σ τ ↔
      (GraphHeadSpec G a σ τ ∨ GraphHeadSpec G b σ τ) := by
  constructor
  · intro h
    cases h with
    | choice_left _ _ _ _ h1 => exact Or.inl h1
    | choice_right _ _ _ _ h2 => exact Or.inr h2
  · intro h
    rcases h with h1 | h2
    · exact GraphHeadSpec.choice_left a b σ τ h1
    · exact GraphHeadSpec.choice_right a b σ τ h2

/-- Spec clause for recursive references: the contribution of `ref i` is
    the contribution of the node label. -/
theorem graphHeadSpec_ref_iff (G : ProcessGraph schema) (i : NodeId) (σ τ : schema.Packet) :
    GraphHeadSpec G (.ref i) σ τ ↔ GraphHeadSpec G (G.label i) σ τ := by
  constructor
  · intro h
    cases h with
    | ref_of _ _ _ h => exact h
  · exact GraphHeadSpec.ref_of i σ τ

/-- The specification is exactly the union of the semantics of the
    NetKAT policies occurring at head-reachable packet-prefix
    positions. -/
theorem graphHeadSpec_iff_prefix (G : ProcessGraph schema) (gp : GProc schema) (σ τ : schema.Packet) :
    GraphHeadSpec G gp σ τ ↔ ∃ N, HeadPrefixOf G gp N ∧ Semantics N σ τ := by
  constructor
  · intro h
    induction h with
    | nSeq_of_sem N cont σ' τ' hsem => exact ⟨N, HeadPrefixOf.here N cont, hsem⟩
    | nSeq_of_tail N cont σ' τ' _ ih =>
        obtain ⟨M, hpre, hsem⟩ := ih
        exact ⟨M, HeadPrefixOf.nSeq N cont M hpre, hsem⟩
    | choice_left a b σ' τ' _ ih =>
        obtain ⟨M, hpre, hsem⟩ := ih
        exact ⟨M, HeadPrefixOf.choice_left a b M hpre, hsem⟩
    | choice_right a b σ' τ' _ ih =>
        obtain ⟨M, hpre, hsem⟩ := ih
        exact ⟨M, HeadPrefixOf.choice_right a b M hpre, hsem⟩
    | ref_of i σ' τ' _ ih =>
        obtain ⟨M, hpre, hsem⟩ := ih
        exact ⟨M, HeadPrefixOf.ref i M hpre, hsem⟩
  · rintro ⟨N, hpre, hsem⟩
    revert hsem
    induction hpre with
    | here N' cont =>
        intro hsem'
        exact GraphHeadSpec.nSeq_of_sem N' cont σ τ hsem'
    | nSeq N' cont M _ ih =>
        intro hsem'
        exact GraphHeadSpec.nSeq_of_tail N' cont σ τ (ih hsem')
    | choice_left a b M _ ih =>
        intro hsem'
        exact GraphHeadSpec.choice_left a b σ τ (ih hsem')
    | choice_right a b M _ ih =>
        intro hsem'
        exact GraphHeadSpec.choice_right a b σ τ (ih hsem')
    | ref i M _ ih =>
        intro hsem'
        exact GraphHeadSpec.ref_of i σ τ (ih hsem')

/-- Prefix occurrences lift through head reachability: a prefix in the
    label of a reachable node is a prefix of the reachable term. -/
theorem headPrefixOf_lift {G : ProcessGraph schema} {root : GProc schema} {j : NodeId}
    (h : HeadPathTo G root j) :
    ∀ N : NetKAT schema, HeadPrefixOf G (G.label j) N → HeadPrefixOf G root N := by
  induction h with
  | ref i => intro N hpre; exact HeadPrefixOf.ref i N hpre
  | nSeq N' cont k _ ih => intro N hpre; exact HeadPrefixOf.nSeq N' cont N (ih N hpre)
  | choice_left a b k _ ih =>
      intro N hpre; exact HeadPrefixOf.choice_left a b N (ih N hpre)
  | choice_right a b k _ ih =>
      intro N hpre; exact HeadPrefixOf.choice_right a b N (ih N hpre)
  | ref_step i k _ ih => intro N hpre; exact HeadPrefixOf.ref i N (ih N hpre)

------------------------------------------------------------------------
-- §5 The independent relational specification
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §6 Local soundness of the collection
--
-- Every packet pair in the semantics of a successful local collection
-- is contributed by a packet-processing prefix of the term's head
-- region.  (Pre-existing S6B work, adapted to the local `headCollect`.)
------------------------------------------------------------------------
/-- Soundness of the collection: every packet pair in the semantics of a
    successful collection is contributed by a head-reachable packet
    prefix. -/
theorem headCollect_prefix_sound (G : ProcessGraph schema) :
    ∀ (gp : GProc schema) (H : NetKAT schema), headCollect gp = some H →
      ∀ σ τ : schema.Packet, Semantics H σ τ →
        ∃ N, HeadPrefixOf G gp N ∧ Semantics N σ τ := by
  intro gp
  cases gp with
  | deadlock =>
      intro H h σ τ hsem
      rw [headCollect_deadlock, Option.some.injEq] at h
      subst h
      exact absurd hsem (sem_drop_empty σ τ)
  | nSeq N cont =>
      intro H h σ τ hsem
      obtain ⟨H', h', hH⟩ := headCollect_nSeq_inv N cont H h
      subst hH
      rcases (union_sem N H' σ τ).mp hsem with hN | hH'
      · exact ⟨N, HeadPrefixOf.here N cont, hN⟩
      · obtain ⟨M, hpre, hsem'⟩ :=
          headCollect_prefix_sound G cont H' h' σ τ hH'
        exact ⟨M, HeadPrefixOf.nSeq N cont M hpre, hsem'⟩
  | recv x N cont =>
      intro H h σ τ hsem
      rw [headCollect_recv] at h
      exact Option.noConfusion h
  | send x N cont =>
      intro H h σ τ hsem
      rw [headCollect_send] at h
      exact Option.noConfusion h
  | rcfgPrefix x N cont =>
      intro H h σ τ hsem
      rw [headCollect_rcfgPrefix, Option.some.injEq] at h
      subst h
      exact absurd hsem (sem_drop_empty σ τ)
  | parallel a b =>
      intro H h σ τ hsem
      rw [headCollect_parallel] at h
      exact Option.noConfusion h
  | choice a b =>
      intro H h σ τ hsem
      obtain ⟨H₁, H₂, ha, hb, hH⟩ := headCollect_choice_inv a b H h
      subst hH
      rcases (union_sem H₁ H₂ σ τ).mp hsem with h₁ | h₂
      · obtain ⟨M, hpre, hsem'⟩ := headCollect_prefix_sound G a H₁ ha σ τ h₁
        exact ⟨M, HeadPrefixOf.choice_left a b M hpre, hsem'⟩
      · obtain ⟨M, hpre, hsem'⟩ := headCollect_prefix_sound G b H₂ hb σ τ h₂
        exact ⟨M, HeadPrefixOf.choice_right a b M hpre, hsem'⟩
  | leftMerge a b =>
      intro H h σ τ hsem
      rw [headCollect_leftMerge] at h
      exact Option.noConfusion h
  | commMerge a b =>
      intro H h σ τ hsem
      rw [headCollect_commMerge] at h
      exact Option.noConfusion h
  | restrict L cont =>
      intro H h σ τ hsem
      rw [headCollect_restrict] at h
      exact Option.noConfusion h
  | project n cont =>
      intro H h σ τ hsem
      rw [headCollect_project] at h
      exact Option.noConfusion h
  | ref i =>
      intro H h σ τ hsem
      rw [headCollect_ref, Option.some.injEq] at h
      subst h
      exact absurd hsem (sem_drop_empty σ τ)

------------------------------------------------------------------------
-- §7 The supported domain
------------------------------------------------------------------------

/-- The shape of a term on which head extraction is supported: the
    paper's four equations (29)-(32) cover `deadlock`, `nSeq`, `choice`
    and `rcfgPrefix`; a recursive reference is supported when it points
    at a live node of the graph. -/
inductive HeadShapeOk {schema : NetKAT.PacketSchema} (G : ProcessGraph schema) : GProc schema → Prop
  | deadlock : HeadShapeOk G .deadlock
  | nSeq (N : NetKAT schema) (cont : GProc schema) : HeadShapeOk G (.nSeq N cont)
  | choice (a b : GProc schema) : HeadShapeOk G (.choice a b)
  | rcfgPrefix (x : Channel) (N : NetKAT schema) (cont : GProc schema) :
      HeadShapeOk G (.rcfgPrefix x N cont)
  | ref (i : NodeId) (h : i ∈ G.nodes) : HeadShapeOk G (.ref i)

/-- The process shapes on which head extraction explicitly fails: the
    communication prefixes (excluded by the paper's restriction
    precondition — they are NOT deadlock), the three merge operators,
    restriction and projection. -/
inductive HeadUnsupported {schema : NetKAT.PacketSchema} : GProc schema → Prop
  | recv (x : Channel) (N : NetKAT schema) (cont : GProc schema) :
      HeadUnsupported (.recv x N cont)
  | send (x : Channel) (N : NetKAT schema) (cont : GProc schema) :
      HeadUnsupported (.send x N cont)
  | parallel (a b : GProc schema) : HeadUnsupported (.parallel a b)
  | leftMerge (a b : GProc schema) : HeadUnsupported (.leftMerge a b)
  | commMerge (a b : GProc schema) : HeadUnsupported (.commMerge a b)
  | restrict (L : Set (CommunicationAction schema)) (cont : GProc schema) :
      HeadUnsupported (.restrict L cont)
  | project (n : Nat) (cont : GProc schema) : HeadUnsupported (.project n cont)

/-- The seven unsupported shapes are outside every supported domain. -/
theorem headUnsupported_not_shapeOk {G : ProcessGraph schema} {dst : GProc schema}
    (h : HeadUnsupported dst) : ¬ HeadShapeOk G dst := by
  cases h with
  | recv x N cont => intro hok; cases hok
  | send x N cont => intro hok; cases hok
  | parallel a b => intro hok; cases hok
  | leftMerge a b => intro hok; cases hok
  | commMerge a b => intro hok; cases hok
  | restrict L cont => intro hok; cases hok
  | project n cont => intro hok; cases hok

/-- Every head reference of a term occurs as a `ref` subterm in its
    head region. -/
theorem headSub_of_headRefs (G : ProcessGraph schema) :
    ∀ (gp : GProc schema) (i : NodeId), i ∈ headRefs gp → HeadSub G gp (.ref i) := by
  intro gp
  cases gp with
  | deadlock => intro i hi; simp [headRefs] at hi
  | nSeq N cont =>
      intro i hi
      simp only [headRefs] at hi
      exact HeadSub.nSeq N cont _ (headSub_of_headRefs G cont i hi)
  | recv x N cont => intro i hi; simp [headRefs] at hi
  | send x N cont => intro i hi; simp [headRefs] at hi
  | rcfgPrefix x N cont => intro i hi; simp [headRefs] at hi
  | parallel a b => intro i hi; simp [headRefs] at hi
  | choice a b =>
      intro i hi
      simp only [headRefs, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact HeadSub.choice_left a b _ (headSub_of_headRefs G a i hi)
      · exact HeadSub.choice_right a b _ (headSub_of_headRefs G b i hi)
  | leftMerge a b => intro i hi; simp [headRefs] at hi
  | commMerge a b => intro i hi; simp [headRefs] at hi
  | restrict L cont => intro i hi; simp [headRefs] at hi
  | project n cont => intro i hi; simp [headRefs] at hi
  | ref i' =>
      intro i hi
      simp only [headRefs, Finset.mem_singleton] at hi
      subst hi
      exact HeadSub.refl _

/-- Ref-free head-subterm containment shrinks through an `nSeq`
    constructor. -/
theorem headSubFree_shrink_nSeq (G : ProcessGraph schema) :
    ∀ (ct X : GProc schema), HeadSubFree G ct X →
      ∀ (N : NetKAT schema) (cont : GProc schema), X = .nSeq N cont →
        HeadSubFree G ct cont := by
  intro ct X hs
  induction hs with
  | refl gp =>
      intro N cont heq
      subst heq
      exact HeadSubFree.nSeq N cont cont (HeadSubFree.refl cont)
  | nSeq N' cont' sub' _ ih =>
      intro N cont heq
      exact HeadSubFree.nSeq N' cont' cont (ih N cont heq)
  | choice_left a b sub' _ ih =>
      intro N cont heq
      exact HeadSubFree.choice_left a b cont (ih N cont heq)
  | choice_right a b sub' _ ih =>
      intro N cont heq
      exact HeadSubFree.choice_right a b cont (ih N cont heq)

/-- Ref-free head-subterm containment shrinks through a `choice`
    constructor (left branch). -/
theorem headSubFree_shrink_choice_left (G : ProcessGraph schema) :
    ∀ (ct X : GProc schema), HeadSubFree G ct X →
      ∀ (a b : GProc schema), X = .choice a b → HeadSubFree G ct a := by
  intro ct X hs
  induction hs with
  | refl gp =>
      intro a b heq
      subst heq
      exact HeadSubFree.choice_left a b a (HeadSubFree.refl a)
  | nSeq N cont sub' _ ih =>
      intro a b heq
      exact HeadSubFree.nSeq N cont a (ih a b heq)
  | choice_left a' b' sub' _ ih =>
      intro a b heq
      exact HeadSubFree.choice_left a' b' a (ih a b heq)
  | choice_right a' b' sub' _ ih =>
      intro a b heq
      exact HeadSubFree.choice_right a' b' a (ih a b heq)

/-- Ref-free head-subterm containment shrinks through a `choice`
    constructor (right branch). -/
theorem headSubFree_shrink_choice_right (G : ProcessGraph schema) :
    ∀ (ct X : GProc schema), HeadSubFree G ct X →
      ∀ (a b : GProc schema), X = .choice a b → HeadSubFree G ct b := by
  intro ct X hs
  induction hs with
  | refl gp =>
      intro a b heq
      subst heq
      exact HeadSubFree.choice_right a b b (HeadSubFree.refl b)
  | nSeq N cont sub' _ ih =>
      intro a b heq
      exact HeadSubFree.nSeq N cont b (ih a b heq)
  | choice_left a' b' sub' _ ih =>
      intro a b heq
      exact HeadSubFree.choice_left a' b' b (ih a b heq)
  | choice_right a' b' sub' _ ih =>
      intro a b heq
      exact HeadSubFree.choice_right a' b' b (ih a b heq)

/-- Failure analysis: if the collection of a term fails, then an
    explicitly unsupported shape is reachable in the term's head
    region.  (References never fail, so no side condition on the
    references is needed.) -/
theorem headCollect_none_failure (G : ProcessGraph schema) :
    ∀ gp : GProc schema, headCollect gp = none →
      ∃ dst, HeadSub G gp dst ∧ HeadUnsupported dst := by
  intro gp
  cases gp with
  | deadlock =>
      intro h; rw [headCollect_deadlock] at h; exact Option.noConfusion h
  | nSeq N cont =>
      intro h
      rw [headCollect_nSeq, Option.map_eq_none_iff] at h
      obtain ⟨dst, hdst, hunsup⟩ := headCollect_none_failure G cont h
      exact ⟨dst, HeadSub.nSeq N cont dst hdst, hunsup⟩
  | recv x N cont =>
      intro _; exact ⟨_, HeadSub.refl _, HeadUnsupported.recv x N cont⟩
  | send x N cont =>
      intro _; exact ⟨_, HeadSub.refl _, HeadUnsupported.send x N cont⟩
  | rcfgPrefix x N cont =>
      intro h; rw [headCollect_rcfgPrefix] at h; exact Option.noConfusion h
  | parallel a b =>
      intro _; exact ⟨_, HeadSub.refl _, HeadUnsupported.parallel a b⟩
  | choice a b =>
      intro h
      rw [headCollect_choice] at h
      cases ha : headCollect a with
      | none =>
          obtain ⟨dst, hdst, hunsup⟩ := headCollect_none_failure G a ha
          exact ⟨dst, HeadSub.choice_left a b dst hdst, hunsup⟩
      | some H₁ =>
          rw [ha] at h
          have h' : (headCollect b).map (fun H₂ => NetKAT.union H₁ H₂) = none := h
          rw [Option.map_eq_none_iff] at h'
          obtain ⟨dst, hdst, hunsup⟩ := headCollect_none_failure G b h'
          exact ⟨dst, HeadSub.choice_right a b dst hdst, hunsup⟩
  | leftMerge a b =>
      intro _; exact ⟨_, HeadSub.refl _, HeadUnsupported.leftMerge a b⟩
  | commMerge a b =>
      intro _; exact ⟨_, HeadSub.refl _, HeadUnsupported.commMerge a b⟩
  | restrict L cont =>
      intro _; exact ⟨_, HeadSub.refl _, HeadUnsupported.restrict L cont⟩
  | project n cont =>
      intro _; exact ⟨_, HeadSub.refl _, HeadUnsupported.project n cont⟩
  | ref i =>
      intro h; rw [headCollect_ref] at h; exact Option.noConfusion h

/-- The supported domain of graph-native head extraction: every term in
    the head region of the root has a supported shape, and every
    head-reachable node is a live node of the graph.  For the root of a
    well-formed graph the second condition is exactly `root_closed` +
    `closed` (see `headPathTo_nodes_closed`). -/
def GraphHeadSupported (G : ProcessGraph schema) : Prop :=
  (∀ dst, HeadSub G G.root dst → HeadShapeOk G dst) ∧
  (∀ j, HeadPathTo G G.root j → j ∈ G.nodes)

/-- **Supported-domain characterization**: on the supported domain the
    extraction always succeeds. -/
theorem graphHead_supported_some (G : ProcessGraph schema)
    (hsupported : GraphHeadSupported G) :
    ∃ H : NetKAT schema, graphHead G = some H := by
  obtain ⟨hshape, hnodes⟩ := hsupported
  obtain ⟨L, hL⟩ : ∃ L, headRun G (headRefsList G.root) ∅ [] = some L := by
    cases hrun : headRun G (headRefsList G.root) ∅ [] with
    | none =>
        obtain ⟨j, hj, hjn⟩ := headRun_root_failure G hrun
        exact absurd (hnodes j hj) hjn
    | some L => exact ⟨L, rfl⟩
  obtain ⟨H₀, hH₀⟩ : ∃ H₀, headCollect G.root = some H₀ := by
    cases hc : headCollect G.root with
    | none =>
        obtain ⟨dst, hdst, hunsup⟩ := headCollect_none_failure G G.root hc
        exact absurd (hshape dst hdst) (headUnsupported_not_shapeOk hunsup)
    | some H₀ => exact ⟨H₀, rfl⟩
  have hall : ∀ j, j ∈ L → ∃ Hⱼ, headCollect (G.label j) = some Hⱼ := by
    intro j hj
    cases hc : headCollect (G.label j) with
    | none =>
        obtain ⟨hpath, _⟩ := (headRun_root_success G L hL).2 j hj
        obtain ⟨dst, hdst, hunsup⟩ := headCollect_none_failure G (G.label j) hc
        exact absurd (hshape dst (HeadSub.trans (headPathTo_sub hpath) hdst))
          (headUnsupported_not_shapeOk hunsup)
    | some Hⱼ => exact ⟨Hⱼ, rfl⟩
  have hgraph : graphHead G = graphHeadUnion G L (headCollect G.root) := by
    simp only [graphHead, hL]
  obtain ⟨H, hH⟩ := unionOverList_some (fun j => headCollect (G.label j)) L
    (headCollect G.root) H₀ hH₀ hall
  exact ⟨H, by rw [hgraph]; exact hH⟩

/-- For the root of a well-formed graph, the node-closure assumption of
    `GraphHeadSupported` is exactly `root_closed` + `closed`. -/
theorem graphHead_supported_some_root (G : ProcessGraph schema)
    (hshape : ∀ dst, HeadSub G G.root dst → HeadShapeOk G dst) :
    ∃ H : NetKAT schema, graphHead G = some H :=
  graphHead_supported_some G ⟨hshape, fun j hj => headPathTo_nodes_closed G j hj⟩

------------------------------------------------------------------------
-- §8 Semantic soundness of `graphHead` (S6B Part 3A)
--
-- `graphHead_sound`: every packet pair in the semantics of a
-- successfully extracted head policy satisfies `GraphHeadSpec G G.root`
-- — the union of the semantics of the NetKAT policies occurring at
-- packet-processing prefixes reachable from the root before any
-- reconfiguration boundary.
--
-- Architecture (each step reuses the existing infrastructure):
--   1. `headCollect_prefix_sound` — a successful local collection is
--      sound: its packet pairs come from a `HeadPrefixOf` witness.
--   2. `headPrefixOf_headSub_lift` — prefix occurrences lift through
--      `HeadSub` containment, so the collection of the root and the
--      collection of any head-reachable node's label are sound AT the
--      root (`HeadPathTo` gives `HeadSub G G.root (G.label j)` via
--      `headPathTo_sub`).
--   3. `unionOverList_sem_decomp` — every packet pair of the
--      successfully folded union comes either from the start value
--      (the root's collection) or from exactly one visited node's
--      collection.
--   4. `headRun_root_success` — the visited list contains EXACTLY the
--      head-reachable nodes, so every node contribution is legitimate.
--
-- Cycles: the worklist visits each node exactly once and a reference
-- contributes `.drop` locally (its label is collected separately), so
-- a cyclic graph neither duplicates contributions nor introduces
-- spurious ones — every contribution is accounted for by a
--     head-reachable node, which is all soundness requires.  (Completeness
--     is established in §9.)
------------------------------------------------------------------------

/-- Prefix occurrences lift through head-subterm containment: a policy
    occurring at a packet-prefix position of a head-subterm occurs at a
    packet-prefix position of the containing term. -/
theorem headPrefixOf_headSub_lift {G : ProcessGraph schema} {root gp : GProc schema}
    (hsub : HeadSub G root gp) {N : NetKAT schema} (hpre : HeadPrefixOf G gp N) :
    HeadPrefixOf G root N := by
  obtain ⟨cont, hc⟩ := (headPrefixOf_iff_headSub G gp N).mp hpre
  exact (headPrefixOf_iff_headSub G root N).mpr ⟨cont, HeadSub.trans hsub hc⟩

/-- Soundness of the local collection relative to any containing head
    term: the packet pairs of a successful collection of `gp` satisfy
    the specification of any term whose head region contains `gp`. -/
theorem headCollect_headSub_spec_sound (G : ProcessGraph schema) {root gp : GProc schema}
    (hsub : HeadSub G root gp) {H : NetKAT schema} (hcol : headCollect gp = some H)
    (σ τ : schema.Packet) (hsem : Semantics H σ τ) :
    GraphHeadSpec G root σ τ := by
  obtain ⟨N, hpre, hNsem⟩ := headCollect_prefix_sound G gp H hcol σ τ hsem
  exact (graphHeadSpec_iff_prefix G root σ τ).mpr
    ⟨N, headPrefixOf_headSub_lift hsub hpre, hNsem⟩

/-- Soundness of the root's local collection (the start value of the
    fold): its packet pairs satisfy the specification of the root. -/
theorem headCollect_root_spec_sound (G : ProcessGraph schema) {H : NetKAT schema}
    (hcol : headCollect G.root = some H) (σ τ : schema.Packet)
    (hsem : Semantics H σ τ) : GraphHeadSpec G G.root σ τ :=
  headCollect_headSub_spec_sound G (HeadSub.refl G.root) hcol σ τ hsem

/-- Soundness of one node's contribution: the local collection of the
    label of a head-reachable node is sound AT the root, because head
    reachability (`HeadPathTo`) makes the node label a head-subterm of
    the root (`headPathTo_sub`). -/
theorem headCollect_node_spec_sound (G : ProcessGraph schema) (j : NodeId)
    {Hⱼ : NetKAT schema} (hpath : HeadPathTo G G.root j)
    (hcol : headCollect (G.label j) = some Hⱼ) (σ τ : schema.Packet)
    (hsem : Semantics Hⱼ σ τ) : GraphHeadSpec G G.root σ τ :=
  headCollect_headSub_spec_sound G (headPathTo_sub hpath) hcol σ τ hsem

/-- Soundness of the completed worklist collection: if the traversal
    succeeded with `L` and the union fold combined the root's local
    collection with the local collections of the visited labels into
    `H`, then every packet pair of `H` satisfies the specification of
    the root.  Each contribution is either the root's own or the label
    of a visited node, and visited nodes are head-reachable
    (`headRun_root_success`), so no contribution escapes the
    specification — regardless of cycles in the reference structure. -/
theorem graphHeadUnion_sound (G : ProcessGraph schema) (L : List NodeId) (H : NetKAT schema)
    (hrun : headRun G (headRefsList G.root) ∅ [] = some L)
    (hfold : graphHeadUnion G L (headCollect G.root) = some H)
    (σ τ : schema.Packet) (hsem : Semantics H σ τ) :
    GraphHeadSpec G G.root σ τ := by
  obtain ⟨_, hlive⟩ := headRun_root_success G L hrun
  obtain ⟨H₀, hcol⟩ : ∃ H₀, headCollect G.root = some H₀ := by
    cases hcol : headCollect G.root with
    | none =>
        rw [hcol] at hfold
        rw [graphHeadUnion] at hfold
        rw [unionOverList_none (fun j => headCollect (G.label j)) L] at hfold
        exact Option.noConfusion hfold
    | some H₀ => exact ⟨H₀, rfl⟩
  rw [graphHeadUnion, hcol] at hfold
  rcases unionOverList_sem_decomp (fun j => headCollect (G.label j)) σ τ L H₀ H
      hfold hsem with hroot | ⟨j, hj, Hⱼ, hfj, hsemⱼ⟩
  · exact headCollect_root_spec_sound G hcol σ τ hroot
  · exact headCollect_node_spec_sound G j (hlive j hj).1 hfj σ τ hsemⱼ

/-- **Semantic soundness of graph-native head extraction**: every
    NetKAT policy produced by `graphHead` has exactly the behavior
    prescribed by the specification, in the inclusion sense: whenever
    `graphHead G = some H`, the semantics of `H` is included in the
    behavior described by `GraphHeadSpec G G.root`.  (Completeness —
    the converse inclusion — is `graphHead_complete` in §9.) -/
theorem graphHead_sound (G : ProcessGraph schema) (H : NetKAT schema)
    (hhead : graphHead G = some H) :
    ∀ σ τ : schema.Packet, Semantics H σ τ → GraphHeadSpec G G.root σ τ := by
  intro σ τ hsem
  cases hrun : headRun G (headRefsList G.root) ∅ [] with
  | none =>
      have hhead' : graphHead G = none := by simp only [graphHead, hrun]
      rw [hhead'] at hhead
      exact Option.noConfusion hhead
  | some L =>
      have hhead' : graphHead G = graphHeadUnion G L (headCollect G.root) := by
        simp only [graphHead, hrun]
      rw [hhead'] at hhead
      exact graphHeadUnion_sound G L H hrun hhead σ τ hsem

/-- Packaged soundness on the supported domain: on a supported graph the
    extraction succeeds AND its result is spec-sound. -/
theorem graphHead_sound_of_supported (G : ProcessGraph schema)
    (hsupported : GraphHeadSupported G) :
    ∃ H : NetKAT schema, graphHead G = some H ∧
      ∀ σ τ : schema.Packet, Semantics H σ τ → GraphHeadSpec G G.root σ τ := by
  obtain ⟨H, hH⟩ := graphHead_supported_some G hsupported
  exact ⟨H, hH, graphHead_sound G H hH⟩

------------------------------------------------------------------------
-- §9 Semantic completeness of `graphHead` (S6B Part 3B)
--
-- `graphHead_complete`: every packet pair described by the relational
-- specification `GraphHeadSpec G G.root` lies in the semantics of the
-- extracted policy, whenever the extraction succeeds.  Together with
-- `graphHead_sound` (S6B Part 3A) this yields the specification
-- equivalence `graphHead_spec_iff` on the supported domain.
--
-- Architecture (each step reuses the existing infrastructure):
--   1. `HeadPrefixOfFree` and `headCollect_prefix_complete` — LOCAL
--      completeness of the collection, opposite in direction to
--      `headCollect_prefix_sound`: every packet pair contributed by a
--      REF-FREE prefix occurrence lies in the semantics of the local
--      collection.  The unrestricted converse of
--      `headCollect_prefix_sound` is false: an occurrence behind a
--      reference is not covered by the referring term's own collection
--      (a reference contributes `.drop` locally); it is covered by the
--      referenced node's collection, which is exactly the contribution
--      the worklist fold adds.
--   2. `headSub_collection_point` — every head-subterm occurrence is
--      reached from its anchor by ref-free steps followed by at most one
--      final reference jump, so every occurrence has a collection point:
--      the anchor itself or the label of a head-reachable node.
--   3. `unionOverList_start_some`, `unionOverList_start_cover`,
--      `unionOverList_mem_cover` — the fold covers the start value and
--      every visited node's contribution.
--   4. `headRun_root_success` — the visited list contains EXACTLY the
--      head-reachable nodes, so every collection point of the second
--      kind is a visited node.
--
-- Supportedness is NOT needed for the completeness direction itself:
-- the success hypothesis `graphHead G = some H` already entails that the
-- root collection and the collection of every visited label succeeded.
-- Supportedness (`GraphHeadSupported`, or its weaker shape-only root
-- condition — see `graphHead_supported_some_root`, which derives the
-- node closure from the graph's own `root_closed`/`closed` fields) is
-- needed only to GUARANTEE that some `H` exists, i.e. for the packaged
-- existence statement and the equivalence theorem.  Without it the
-- equivalence genuinely fails: a reachable unsupported constructor makes
-- `graphHead` fail (`none`) while the specification can still be
-- nonempty (witnessed by the test fixture in `test_graph_head.lean`).
------------------------------------------------------------------------

/-- Ref-free prefix occurrence: `N` occurs at a packet-prefix position of
    `gp` reachable without crossing any reference edge.  This is exactly
    the fragment of `HeadPrefixOf` that `headCollect` covers locally;
    occurrences behind references are covered at the referenced node's
    label instead. -/
inductive HeadPrefixOfFree {schema : NetKAT.PacketSchema} (G : ProcessGraph schema) : GProc schema → NetKAT schema → Prop
  | here (N : NetKAT schema) (cont : GProc schema) : HeadPrefixOfFree G (.nSeq N cont) N
  | nSeq (N : NetKAT schema) (cont : GProc schema) (M : NetKAT schema)
      (h : HeadPrefixOfFree G cont M) : HeadPrefixOfFree G (.nSeq N cont) M
  | choice_left (a b : GProc schema) (M : NetKAT schema)
      (h : HeadPrefixOfFree G a M) : HeadPrefixOfFree G (.choice a b) M
  | choice_right (a b : GProc schema) (M : NetKAT schema)
      (h : HeadPrefixOfFree G b M) : HeadPrefixOfFree G (.choice a b) M

/-- Ref-free prefix occurrences are prefix occurrences. -/
theorem headPrefixOfFree_to_headPrefixOf {G : ProcessGraph schema} {gp : GProc schema}
    {N : NetKAT schema} (h : HeadPrefixOfFree G gp N) : HeadPrefixOf G gp N := by
  induction h with
  | here N cont => exact HeadPrefixOf.here N cont
  | nSeq N cont M _ ih => exact HeadPrefixOf.nSeq N cont M ih
  | choice_left a b M _ ih => exact HeadPrefixOf.choice_left a b M ih
  | choice_right a b M _ ih => exact HeadPrefixOf.choice_right a b M ih

/-- A ref-free head-subterm of the shape `N; cont` witnesses a ref-free
    prefix occurrence (counterpart of `headPrefixOf_of_headSub`). -/
theorem headPrefixOfFree_of_headSubFree (G : ProcessGraph schema) :
    ∀ (gp sub : GProc schema), HeadSubFree G gp sub →
      ∀ (N : NetKAT schema) (cont : GProc schema), sub = .nSeq N cont →
        HeadPrefixOfFree G gp N := by
  intro gp sub hs
  induction hs with
  | refl gp =>
      intro N cont heq
      subst heq
      exact HeadPrefixOfFree.here N cont
  | nSeq N' cont' sub' _ ih =>
      intro N cont heq
      exact HeadPrefixOfFree.nSeq N' cont' N (ih N cont heq)
  | choice_left a b sub' _ ih =>
      intro N cont heq
      exact HeadPrefixOfFree.choice_left a b N (ih N cont heq)
  | choice_right a b sub' _ ih =>
      intro N cont heq
      exact HeadPrefixOfFree.choice_right a b N (ih N cont heq)

/-- Characterization of ref-free prefix occurrences by ref-free
    head-subterms of the shape `N; cont` (counterpart of
    `headPrefixOf_iff_headSub`). -/
theorem headPrefixOfFree_iff_headSubFree (G : ProcessGraph schema) (gp : GProc schema)
    (N : NetKAT schema) :
    HeadPrefixOfFree G gp N ↔ ∃ cont : GProc schema, HeadSubFree G gp (.nSeq N cont) := by
  constructor
  · intro h
    induction h with
    | here N cont => exact ⟨cont, HeadSubFree.refl (.nSeq N cont)⟩
    | nSeq N cont M _ ih =>
        obtain ⟨cont'', hs⟩ := ih
        exact ⟨cont'', HeadSubFree.nSeq N cont (.nSeq M cont'') hs⟩
    | choice_left a b M _ ih =>
        obtain ⟨cont'', hs⟩ := ih
        exact ⟨cont'', HeadSubFree.choice_left a b (.nSeq M cont'') hs⟩
    | choice_right a b M _ ih =>
        obtain ⟨cont'', hs⟩ := ih
        exact ⟨cont'', HeadSubFree.choice_right a b (.nSeq M cont'') hs⟩
  · rintro ⟨cont, hs⟩
    exact headPrefixOfFree_of_headSubFree G gp _ hs N cont rfl

/-- **Local completeness of the collection** (S6B Part 3B): the direction
    opposite to `headCollect_prefix_sound`, on its exact domain of
    validity.  Every packet pair contributed by a ref-free prefix
    occurrence lies in the semantics of the local collection — provided
    the collection succeeds.  (Occurrences behind references are covered
    by the referenced node's own collection; see
    `headSub_collection_point` and `graphHead_complete`.  `HeadShapeOk`
    is not needed here: success of the collection is the hypothesis, and
    on the supported domain success is guaranteed by
    `graphHead_supported_some` via `headCollect_none_failure`.) -/
theorem headCollect_prefix_complete (G : ProcessGraph schema) :
    ∀ (gp : GProc schema) (N : NetKAT schema), HeadPrefixOfFree G gp N →
      ∀ σ τ : schema.Packet, Semantics N σ τ →
        ∀ H : NetKAT schema, headCollect gp = some H → Semantics H σ τ := by
  intro gp N h
  induction h with
  | here N cont =>
      intro σ τ hsem H hcol
      obtain ⟨H', h', hH⟩ := headCollect_nSeq_inv N cont H hcol
      subst hH
      exact (union_sem N H' σ τ).mpr (Or.inl hsem)
  | nSeq N' cont M _ ih =>
      intro σ τ hsem H hcol
      obtain ⟨H', h', hH⟩ := headCollect_nSeq_inv N' cont H hcol
      subst hH
      exact (union_sem N' H' σ τ).mpr (Or.inr (ih σ τ hsem H' h'))
  | choice_left a b M _ ih =>
      intro σ τ hsem H hcol
      obtain ⟨H₁, H₂, ha, hb, hH⟩ := headCollect_choice_inv a b H hcol
      subst hH
      exact (union_sem H₁ H₂ σ τ).mpr (Or.inl (ih σ τ hsem H₁ ha))
  | choice_right a b M _ ih =>
      intro σ τ hsem H hcol
      obtain ⟨H₁, H₂, ha, hb, hH⟩ := headCollect_choice_inv a b H hcol
      subst hH
      exact (union_sem H₁ H₂ σ τ).mpr (Or.inr (ih σ τ hsem H₂ hb))

/-- **Collection-point decomposition**: every head-subterm occurrence is
    reached from its anchor by ref-free head-subterm steps followed by at
    most one final reference jump.  Consequently every prefix occurrence
    has a collection point: either the anchor term itself (ref-free
    occurrence, covered by the anchor's local collection) or the label of
    a node head-reachable from the anchor (covered by that node's local
    collection, which the worklist fold visits exactly once).  The proof
    is a straightforward induction on the `HeadSub` derivation, so no
    acyclicity assumption is involved. -/
theorem headSub_collection_point (G : ProcessGraph schema) :
    ∀ {anchor sub : GProc schema}, HeadSub G anchor sub →
      ∃ cp : GProc schema,
        (cp = anchor ∨ ∃ j, HeadPathTo G anchor j ∧ cp = G.label j) ∧
        HeadSubFree G cp sub := by
  intro anchor sub h
  induction h with
  | refl gp => exact ⟨gp, Or.inl rfl, HeadSubFree.refl gp⟩
  | nSeq N cont sub _ ih =>
      obtain ⟨cp, hcp, hfree⟩ := ih
      rcases hcp with hEq | ⟨j, hj, hcpEq⟩
      · refine ⟨.nSeq N cont, Or.inl rfl, ?_⟩
        rw [hEq] at hfree
        exact HeadSubFree.nSeq N cont sub hfree
      · refine ⟨G.label j, Or.inr ⟨j, HeadPathTo.nSeq N cont j hj, rfl⟩, ?_⟩
        rw [hcpEq] at hfree
        exact hfree
  | choice_left a b sub _ ih =>
      obtain ⟨cp, hcp, hfree⟩ := ih
      rcases hcp with hEq | ⟨j, hj, hcpEq⟩
      · refine ⟨.choice a b, Or.inl rfl, ?_⟩
        rw [hEq] at hfree
        exact HeadSubFree.choice_left a b sub hfree
      · refine ⟨G.label j, Or.inr ⟨j, HeadPathTo.choice_left a b j hj, rfl⟩, ?_⟩
        rw [hcpEq] at hfree
        exact hfree
  | choice_right a b sub _ ih =>
      obtain ⟨cp, hcp, hfree⟩ := ih
      rcases hcp with hEq | ⟨j, hj, hcpEq⟩
      · refine ⟨.choice a b, Or.inl rfl, ?_⟩
        rw [hEq] at hfree
        exact HeadSubFree.choice_right a b sub hfree
      · refine ⟨G.label j, Or.inr ⟨j, HeadPathTo.choice_right a b j hj, rfl⟩, ?_⟩
        rw [hcpEq] at hfree
        exact hfree
  | ref i sub _ ih =>
      obtain ⟨cp, hcp, hfree⟩ := ih
      rcases hcp with hEq | ⟨j, hj, hcpEq⟩
      · refine ⟨G.label i, Or.inr ⟨i, HeadPathTo.ref i, rfl⟩, ?_⟩
        rw [hEq] at hfree
        exact hfree
      · refine ⟨G.label j,
          Or.inr ⟨j, headPathTo_trans (HeadPathTo.ref i) hj, rfl⟩, ?_⟩
        rw [hcpEq] at hfree
        exact hfree

theorem unionStep_none_of_acc_none (f : NodeId → Option (NetKAT schema)) (j : NodeId) :
    unionStep f j none = none := by
  simp only [unionStep]
  cases f j <;> rfl

/-- The start value of a successful fold is successful: if the fold over
    `l` starting from `start` succeeds, then `start` was already `some`. -/
theorem unionOverList_start_some (f : NodeId → Option (NetKAT schema)) :
    ∀ (l : List NodeId) (start : Option (NetKAT schema)) (H : NetKAT schema),
      unionOverList f l start = some H → ∃ H₀, start = some H₀ := by
  intro l
  induction l with
  | nil => intro start H h; exact ⟨H, h⟩
  | cons j js ih =>
      intro start H h
      cases start with
      | none =>
          exfalso
          rw [unionOverList] at h
          rw [unionStep_none_of_acc_none] at h
          rw [unionOverList_none f js] at h
          exact Option.noConfusion h
      | some H₀ => exact ⟨H₀, rfl⟩

/-- **Completeness of the completed worklist collection** (S6B Part 3B):
    if the traversal succeeded with `L` and the union fold combined the
    root's local collection with the local collections of the visited
    labels into `H`, then every packet pair described by the
    specification of the root lies in the semantics of `H`.  Each
    collection point of a specification contribution is either the root
    (whose collection is the fold's start value) or the label of a
    head-reachable node (which the worklist visits exactly once, by
    `headRun_root_success`), and the local collection is complete on
    ref-free occurrences (`headCollect_prefix_complete`).  Cycles need no
    special treatment: the derivation of the specification is finite, so
    the collection point exists after finitely many reference jumps. -/
theorem graphHeadUnion_complete (G : ProcessGraph schema) (L : List NodeId) (H : NetKAT schema)
    (hrun : headRun G (headRefsList G.root) ∅ [] = some L)
    (hfold : graphHeadUnion G L (headCollect G.root) = some H)
    (σ τ : schema.Packet) (hspec : GraphHeadSpec G G.root σ τ) :
    Semantics H σ τ := by
  obtain ⟨hcover, _hlive⟩ := headRun_root_success G L hrun
  rw [graphHeadUnion] at hfold
  obtain ⟨H₀, hcol⟩ : ∃ H₀, headCollect G.root = some H₀ :=
    unionOverList_start_some (fun j => headCollect (G.label j)) L
      (headCollect G.root) H hfold
  have hfold' : unionOverList (fun j => headCollect (G.label j)) L (some H₀) =
      some H := by
    rw [hcol] at hfold
    exact hfold
  have hall : ∀ j, j ∈ L → ∃ Hⱼ, headCollect (G.label j) = some Hⱼ :=
    unionOverList_all_some (fun j => headCollect (G.label j)) L H₀ H hfold'
  obtain ⟨N, hpre, hsem⟩ := (graphHeadSpec_iff_prefix G G.root σ τ).mp hspec
  obtain ⟨cont, hsub⟩ := (headPrefixOf_iff_headSub G G.root N).mp hpre
  obtain ⟨cp, hcp, hcpfree⟩ := headSub_collection_point G hsub
  rcases hcp with hEq | ⟨j, hjpath, hjcp⟩
  · -- the occurrence is ref-free at the root: covered by the start value
    rw [hEq] at hcpfree
    have h₀ : Semantics H₀ σ τ :=
      headCollect_prefix_complete G G.root N
        (headPrefixOfFree_of_headSubFree G G.root _ hcpfree N cont rfl) σ τ hsem
        H₀ hcol
    exact unionOverList_start_cover (fun j => headCollect (G.label j)) σ τ L
      H₀ H hfold' h₀
  · -- the occurrence is ref-free at the label of a head-reachable node
    rw [hjcp] at hcpfree
    have hjL : j ∈ L := hcover j hjpath
    obtain ⟨Hⱼ, hfj⟩ := hall j hjL
    have hⱼ : Semantics Hⱼ σ τ :=
      headCollect_prefix_complete G (G.label j) N
        (headPrefixOfFree_of_headSubFree G (G.label j) _ hcpfree N cont rfl) σ τ
        hsem Hⱼ hfj
    exact unionOverList_mem_cover (fun j => headCollect (G.label j)) σ τ L
      H₀ H hfold' j hjL Hⱼ hfj hⱼ

/-- **Semantic completeness of graph-native head extraction** (S6B Part 3B):
    every NetKAT policy produced by `graphHead` captures the full behavior
    prescribed by the specification: whenever `graphHead G = some H`, the
    behavior described by `GraphHeadSpec G G.root` is included in the
    semantics of `H`.  Together with `graphHead_sound` (S6B Part 3A) the
    extraction is semantically exact whenever it succeeds — no
    supportedness hypothesis is needed beyond the success itself, because
    success already forces every involved local collection to succeed. -/
theorem graphHead_complete (G : ProcessGraph schema) (H : NetKAT schema)
    (hhead : graphHead G = some H) :
    ∀ σ τ : schema.Packet, GraphHeadSpec G G.root σ τ → Semantics H σ τ := by
  intro σ τ hspec
  cases hrun : headRun G (headRefsList G.root) ∅ [] with
  | none =>
      have hhead' : graphHead G = none := by simp only [graphHead, hrun]
      rw [hhead'] at hhead
      exact Option.noConfusion hhead
  | some L =>
      have hhead' : graphHead G = graphHeadUnion G L (headCollect G.root) := by
        simp only [graphHead, hrun]
      rw [hhead'] at hhead
      exact graphHeadUnion_complete G L H hrun hhead σ τ hspec

/-- **Packaged completeness on the supported domain**: on a supported
    graph the extraction succeeds AND its result captures the full
    specification behavior. -/
theorem graphHead_complete_of_supported (G : ProcessGraph schema)
    (hsupported : GraphHeadSupported G) (σ τ : schema.Packet)
    (hspec : GraphHeadSpec G G.root σ τ) :
    ∃ H : NetKAT schema, graphHead G = some H ∧ Semantics H σ τ := by
  obtain ⟨H, hH⟩ := graphHead_supported_some G hsupported
  exact ⟨H, hH, graphHead_complete G H hH σ τ hspec⟩

/-- **Packaged completeness under the weaker shape-only condition**: by
    `graphHead_supported_some_root`, the node-closure conjunct of
    `GraphHeadSupported` is derivable from the graph's own
    `root_closed`/`closed` fields (`headPathTo_nodes_closed`), so only
    the shape condition on the root's head region is needed. -/
theorem graphHead_complete_of_shapeOk_root (G : ProcessGraph schema)
    (hshape : ∀ dst, HeadSub G G.root dst → HeadShapeOk G dst)
    (σ τ : schema.Packet) (hspec : GraphHeadSpec G G.root σ τ) :
    ∃ H : NetKAT schema, graphHead G = some H ∧ Semantics H σ τ := by
  obtain ⟨H, hH⟩ := graphHead_supported_some_root G hshape
  exact ⟨H, hH, graphHead_complete G H hH σ τ hspec⟩

/-- **Specification equivalence** (S6B Part 3B): on the supported domain,
    the relational specification and the extracted policy's semantics
    coincide packet-pair by packet-pair.  The forward direction is
    `graphHead_complete_of_supported`; the reverse direction reuses
    `graphHead_sound` (S6B Part 3A) without duplicating its proof. -/
theorem graphHead_spec_iff (G : ProcessGraph schema)
    (hsupported : GraphHeadSupported G) (σ τ : schema.Packet) :
    GraphHeadSpec G G.root σ τ ↔
      ∃ H : NetKAT schema, graphHead G = some H ∧ Semantics H σ τ := by
  constructor
  · exact graphHead_complete_of_supported G hsupported σ τ
  · rintro ⟨H, hH, hsem⟩
    exact graphHead_sound G H hH σ τ hsem

/-- Specification equivalence under the weaker shape-only condition
    (the node-closure conjunct of `GraphHeadSupported` is redundant for
    well-formed graphs). -/
theorem graphHead_spec_iff_of_shapeOk_root (G : ProcessGraph schema)
    (hshape : ∀ dst, HeadSub G G.root dst → HeadShapeOk G dst) (σ τ : schema.Packet) :
    GraphHeadSpec G G.root σ τ ↔
      ∃ H : NetKAT schema, graphHead G = some H ∧ Semantics H σ τ := by
  constructor
  · exact graphHead_complete_of_shapeOk_root G hshape σ τ
  · rintro ⟨H, hH, hsem⟩
    exact graphHead_sound G H hH σ τ hsem

/-- Reusable supportedness introduction: if an invariant `Inv` holds at
    the anchor, every `Inv` term is shape-ok, and `Inv` is closed under
    the head-region descents (through `nSeq` continuations, `choice`
    branches and live references into node labels), then every
    head-subterm of the anchor is shape-ok.  This discharges the shape
    condition of `GraphHeadSupported` for concrete graphs by a finite
    invariant — cyclic definitions included, since the induction runs on
    the finite `HeadSub` derivation, never on the unfolding. -/
theorem headShapeOk_of_headSub_inv (G : ProcessGraph schema) :
    ∀ (a dst : GProc schema), HeadSub G a dst →
      ∀ Inv : GProc schema → Prop,
        Inv a →
        (∀ b, Inv b → HeadShapeOk G b) →
        (∀ b, Inv b → ∀ (N : NetKAT schema) (cont : GProc schema), b = .nSeq N cont → Inv cont) →
        (∀ b, Inv b → ∀ (x y : GProc schema), b = .choice x y → Inv x ∧ Inv y) →
        (∀ b, Inv b → ∀ (i : NodeId), b = .ref i → i ∈ G.nodes ∧ Inv (G.label i)) →
        HeadShapeOk G dst := by
  intro a dst h
  induction h with
  | refl gp =>
      intro Inv hInv hOk _ _ _
      exact hOk gp hInv
  | nSeq N cont sub _ ih =>
      intro Inv hInv hOk hNSeq hChoice hRef
      refine ih Inv ?_ hOk hNSeq hChoice hRef
      exact hNSeq _ hInv N cont rfl
  | choice_left a b sub _ ih =>
      intro Inv hInv hOk hNSeq hChoice hRef
      refine ih Inv ?_ hOk hNSeq hChoice hRef
      exact (hChoice _ hInv a b rfl).1
  | choice_right a b sub _ ih =>
      intro Inv hInv hOk hNSeq hChoice hRef
      refine ih Inv ?_ hOk hNSeq hChoice hRef
      exact (hChoice _ hInv a b rfl).2
  | ref i sub _ ih =>
      intro Inv hInv hOk hNSeq hChoice hRef
      refine ih Inv ?_ hOk hNSeq hChoice hRef
      exact (hRef _ hInv i rfl).2

------------------------------------------------------------------------
-- §10 Worked examples: the recursive behaviors
--
-- The four required behaviors are witnessed by concrete graphs and
-- executable extraction results:
--   * guarded self-reference `X ≜ N;X`       — semantically `N`;
--   * guarded mutual recursion `X ≜ N;Y`,
--     `Y ≜ M;X`                              — semantically `N + M`;
--   * unguarded cycle `X ≜ Y`, `Y ≜ X`       — `some` empty head
--     (a valid empty head, not an unsupported process);
--   * unreachable recursive definitions      — contribute nothing and
--     cause no failure;
--   * reconfiguration boundary               — references and
--     unsupported constructors after `rcfgPrefix` are not traversed.
------------------------------------------------------------------------

/-- The label function of the self-recursive example `X ≜ N;X`. -/
def exSelfLoopLabel (N : NetKAT) (i : NodeId) : GProc :=
  match i with
  | Sum.inl "X" => .nSeq N (.ref (varNode "X"))
  | _ => .deadlock

/-- Example graph for the self-recursive guarded process `X ≜ N;X`. -/
def exSelfLoopGraph (N : NetKAT) : ProcessGraph where
  nodes := {varNode "X"}
  root := .ref (varNode "X")
  label := exSelfLoopLabel N
  root_closed := by
    intro i hi
    simpa [gprocRefs] using hi
  closed := by
    intro i hi
    have hiX : i = varNode "X" := by simpa using hi
    subst hiX
    intro k hk
    simpa [exSelfLoopLabel, gprocRefs, varNode] using hk

/-- The self-recursive example extracts the policy `0 + (N + 0)`: the
    cycle is traversed exactly once and the local `.drop` of the
    reference contributes nothing. -/
theorem exSelfLoop_extracted (N : NetKAT) :
    graphHead (exSelfLoopGraph N) =
      some (NetKAT.union .drop (NetKAT.union N .drop)) := by
  simp [graphHead, graphHeadUnion, unionOverList, unionStep, headCollect,
    headRun, headRefsList, exSelfLoopGraph, exSelfLoopLabel, varNode]

/-- Its semantics is exactly the semantics of `N`: the expected result
    for `X ≜ N;X`. -/
theorem exSelfLoop_semantic (N : NetKAT) (σ τ : CtxPkt) :
    Semantics (NetKAT.union .drop (NetKAT.union N .drop)) σ τ ↔
      Semantics N σ τ := by
  simp [union_sem, Semantics]

/-- The label function of the mutually recursive example
    `X ≜ N;Y`, `Y ≜ M;X`. -/
def exMutualLabel (N M : NetKAT) (i : NodeId) : GProc :=
  match i with
  | Sum.inl "X" => .nSeq N (.ref (varNode "Y"))
  | Sum.inl "Y" => .nSeq M (.ref (varNode "X"))
  | _ => .deadlock

/-- Example graph for the mutually recursive guarded processes. -/
def exMutualGraph (N M : NetKAT) : ProcessGraph where
  nodes := {varNode "X", varNode "Y"}
  root := .ref (varNode "X")
  label := exMutualLabel N M
  root_closed := by
    intro i hi
    have hi' : i ∈ ({varNode "X"} : Finset NodeId) := by simpa [gprocRefs] using hi
    exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hi'))
  closed := by
    intro i hi
    rcases Finset.mem_insert.mp hi with hiEq | hi'
    · subst hiEq
      intro k hk
      simp only [exMutualLabel, gprocRefs, varNode, Finset.mem_insert,
        Finset.mem_singleton, Finset.not_mem_empty] at hk ⊢
      tauto
    · have hiY : i = varNode "Y" := by simpa using hi'
      subst hiY
      intro k hk
      simp only [exMutualLabel, gprocRefs, varNode, Finset.mem_insert,
        Finset.mem_singleton, Finset.not_mem_empty] at hk ⊢
      tauto

/-- The mutually recursive example extracts `0 + (M + 0) + (N + 0)`:
    both nodes of the cycle are visited exactly once. -/
theorem exMutual_extracted (N M : NetKAT) :
    graphHead (exMutualGraph N M) =
      some (NetKAT.union (NetKAT.union .drop (NetKAT.union M .drop))
        (NetKAT.union N .drop)) := by
  simp [graphHead, graphHeadUnion, unionOverList, unionStep, headCollect,
    headRun, headRefsList, exMutualGraph, exMutualLabel, varNode]

/-- Its semantics is exactly the semantics of `N + M`: the expected
    result for the guarded mutual recursion. -/
theorem exMutual_semantic (N M : NetKAT) (σ τ : CtxPkt) :
    Semantics (NetKAT.union (NetKAT.union .drop (NetKAT.union M .drop))
      (NetKAT.union N .drop)) σ τ ↔ Semantics (NetKAT.union N M) σ τ := by
  simp only [union_sem, Semantics]
  tauto

/-- The label function of the unguarded cycle `X ≜ Y`, `Y ≜ X`. -/
def exUnguardedLabel (i : NodeId) : GProc :=
  match i with
  | Sum.inl "X" => .ref (varNode "Y")
  | Sum.inl "Y" => .ref (varNode "X")
  | _ => .deadlock

/-- Example graph for the unguarded cycle. -/
def exUnguardedGraph : ProcessGraph where
  nodes := {varNode "X", varNode "Y"}
  root := .ref (varNode "X")
  label := exUnguardedLabel
  root_closed := by
    intro i hi
    have hi' : i ∈ ({varNode "X"} : Finset NodeId) := by simpa [gprocRefs] using hi
    exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hi'))
  closed := by
    intro i hi
    rcases Finset.mem_insert.mp hi with hiEq | hi'
    · subst hiEq
      intro k hk
      simp only [exUnguardedLabel, gprocRefs, varNode, Finset.mem_insert,
        Finset.mem_singleton, Finset.not_mem_empty] at hk ⊢
      tauto
    · have hiY : i = varNode "Y" := by simpa using hi'
      subst hiY
      intro k hk
      simp only [exUnguardedLabel, gprocRefs, varNode, Finset.mem_insert,
        Finset.mem_singleton, Finset.not_mem_empty] at hk ⊢
      tauto

/-- The unguarded cycle is SUPPORTED: it extracts the empty head
    `0 + (0 + 0)` — a valid empty head, not an unsupported process. -/
theorem exUnguarded_extracted :
    graphHead exUnguardedGraph =
      some (NetKAT.union (NetKAT.union .drop .drop) .drop) := by
  simp [graphHead, graphHeadUnion, unionOverList, unionStep, headCollect,
    headRun, headRefsList, exUnguardedGraph, exUnguardedLabel, varNode]

/-- Its semantics is the empty relation: a valid empty head. -/
theorem exUnguarded_semantic (σ τ : CtxPkt) :
    ¬ Semantics (NetKAT.union (NetKAT.union .drop .drop) .drop) σ τ := by
  simp [union_sem, Semantics]

/-- The label function of the unreachable-definition example: node `Z`
    carries a recursive definition that is never head-reachable. -/
def exUnreachableLabel (P : NetKAT) (i : NodeId) : GProc :=
  match i with
  | Sum.inl "X" => .deadlock
  | Sum.inl "Z" => .nSeq P (.ref (varNode "Z"))
  | _ => .deadlock

/-- Example graph with an unreachable recursive definition. -/
def exUnreachableGraph (P : NetKAT) : ProcessGraph where
  nodes := {varNode "X", varNode "Z"}
  root := .ref (varNode "X")
  label := exUnreachableLabel P
  root_closed := by
    intro i hi
    have hi' : i ∈ ({varNode "X"} : Finset NodeId) := by simpa [gprocRefs] using hi
    exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hi'))
  closed := by
    intro i hi
    rcases Finset.mem_insert.mp hi with hiEq | hi'
    · subst hiEq
      intro k hk
      simp only [exUnreachableLabel, gprocRefs, varNode, Finset.not_mem_empty] at hk
    · have hiZ : i = varNode "Z" := by simpa using hi'
      subst hiZ
      intro k hk
      simp only [exUnreachableLabel, gprocRefs, varNode, Finset.mem_insert,
        Finset.mem_singleton, Finset.not_mem_empty] at hk ⊢
      tauto

/-- The unreachable recursive definition neither contributes to the
    result nor causes extraction failure. -/
theorem exUnreachable_extracted (P : NetKAT) :
    graphHead (exUnreachableGraph P) =
      some (NetKAT.union .drop .drop) := by
  simp [graphHead, graphHeadUnion, unionOverList, unionStep, headCollect,
    headRun, headRefsList, exUnreachableGraph, exUnreachableLabel, varNode]

theorem exUnreachable_semantic (_P : NetKAT) (σ τ : CtxPkt) :
    ¬ Semantics (NetKAT.union .drop .drop) σ τ := by
  simp [union_sem, Semantics]

/-- The label function of the reconfiguration-boundary example: the
    node referenced after the boundary carries an unsupported shape. -/
def exRcfgLabel (x : Channel) (i : NodeId) : GProc :=
  match i with
  | Sum.inl "X" => .recv x .id .deadlock
  | _ => .deadlock

/-- Example graph with a reconfiguration boundary. -/
def exRcfgGraph (x : Channel) (N : NetKAT) : ProcessGraph where
  nodes := {varNode "X"}
  root := .nSeq N (.rcfgPrefix x .id (.ref (varNode "X")))
  label := exRcfgLabel x
  root_closed := by
    intro i hi
    simpa [gprocRefs] using hi
  closed := by
    intro i hi
    have hiX : i = varNode "X" := by simpa using hi
    subst hiX
    intro k hk
    simp only [exRcfgLabel, gprocRefs, varNode] at hk
    exact absurd hk (Finset.not_mem_empty k)

/-- The reconfiguration boundary stops the traversal: the reference
    after the boundary (whose node label is unsupported) is not
    followed, and the extraction yields `N + 0`. -/
theorem exRcfg_extracted (x : Channel) (N : NetKAT) :
    graphHead (exRcfgGraph x N) = some (NetKAT.union N .drop) := by
  simp [graphHead, graphHeadUnion, unionOverList, unionStep, headCollect,
    headRun, headRefsList, exRcfgGraph, exRcfgLabel, varNode]

theorem exRcfg_semantic (N : NetKAT) (σ τ : CtxPkt) :
    Semantics (NetKAT.union N .drop) σ τ ↔ Semantics N σ τ := by
  simp [union_sem, Semantics]

end DyNetKAT.DyNetKAT
