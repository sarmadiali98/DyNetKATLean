import DyNetKAT.DyNetKAT.ProcessGraph
import DyNetKAT.DyNetKAT.Equations
import DyNetKAT.DyNetKAT.Ground
import DyNetKAT.DyNetKAT.TypedGuardedness
import Mathlib.Logic.Relation

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : NetKAT.PacketSchema}

open Relation

namespace DependencyClosure

abbrev Edge (edges : Finset (Var × Var)) (x y : Var) : Prop := (x, y) ∈ edges

def grow (edges : Finset (Var × Var)) (seen : Finset Var) : Finset Var :=
  seen ∪ ((edges.filter fun e => e.1 ∈ seen).image Prod.snd)

theorem mem_grow {edges : Finset (Var × Var)} {seen : Finset Var} {y : Var} :
    y ∈ grow edges seen ↔ y ∈ seen ∨ ∃ x ∈ seen, Edge edges x y := by
  simp only [grow, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (h | ⟨⟨x, _⟩, ⟨he, hx⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x, hx, he⟩
  · rintro (h | ⟨x, hx, he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(x, y), ⟨he, hx⟩, rfl⟩

def saturate (edges : Finset (Var × Var)) : Nat → Finset Var → Finset Var
  | 0, seen => seen
  | n + 1, seen =>
    let next := grow edges seen
    if next = seen then seen else saturate edges n next

private theorem grow_subset {edges : Finset (Var × Var)} {seen U : Finset Var}
    (bound : ∀ x y, Edge edges x y → y ∈ U) (hs : seen ⊆ U) :
    grow edges seen ⊆ U := by
  intro y hy
  rcases mem_grow.mp hy with h | ⟨x, _, he⟩
  · exact hs h
  · exact bound x y he

private theorem stable {edges : Finset (Var × Var)} {U : Finset Var}
    (bound : ∀ x y, Edge edges x y → y ∈ U)
    (n : Nat) (seen : Finset Var) (hs : seen ⊆ U) (fuel : U.card ≤ seen.card + n) :
    grow edges (saturate edges n seen) = saturate edges n seen := by
  induction n generalizing seen with
  | zero =>
    have full : seen = U := Finset.eq_of_subset_of_card_le hs (by simpa using fuel)
    change grow edges seen = seen
    have sub := grow_subset bound hs
    rw [← full] at sub
    exact Finset.Subset.antisymm sub (fun _ h => mem_grow.mpr (.inl h))
  | succ n ih =>
    have incl : seen ⊆ grow edges seen := fun _ h => mem_grow.mpr (.inl h)
    have sub := grow_subset bound hs
    by_cases same : grow edges seen = seen
    · simp [saturate, same]
    · have inc : seen.card < (grow edges seen).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨incl, Ne.symm same⟩)
      simpa [saturate, same] using ih (grow edges seen) sub (by omega)

private theorem includes (edges : Finset (Var × Var)) (n : Nat) (seen : Finset Var) :
    seen ⊆ saturate edges n seen := by
  induction n generalizing seen with
  | zero => exact fun _ h => h
  | succ n ih =>
    by_cases same : grow edges seen = seen
    · simp [saturate, same]
    · simpa [saturate, same] using
        (show seen ⊆ saturate edges n (grow edges seen) from
          fun _ h => ih _ (mem_grow.mpr (.inl h)))

private theorem sound (edges : Finset (Var × Var)) (n : Nat) (seen : Finset Var)
    {y : Var} (hy : y ∈ saturate edges n seen) :
    ∃ x ∈ seen, ReflTransGen (Edge edges) x y := by
  induction n generalizing seen y with
  | zero => exact ⟨y, hy, .refl⟩
  | succ n ih =>
    by_cases same : grow edges seen = seen
    · exact ⟨y, by simpa [saturate, same] using hy, .refl⟩
    · obtain ⟨x, hx, path⟩ := ih _ (by simpa [saturate, same] using hy)
      rcases mem_grow.mp hx with hx | ⟨z, hz, he⟩
      · exact ⟨x, hx, path⟩
      · exact ⟨z, hz, path.head he⟩

def close (U : Finset Var) (edges : Finset (Var × Var)) (entries : Finset Var) :
    Finset Var := saturate edges U.card entries

theorem mem_close {U : Finset Var} {edges : Finset (Var × Var)} {entries : Finset Var}
    (bound : ∀ x y, Edge edges x y → y ∈ U) (hs : entries ⊆ U) {y : Var} :
    y ∈ close U edges entries ↔ ∃ x ∈ entries, ReflTransGen (Edge edges) x y := by
  constructor
  · exact sound edges U.card entries
  · rintro ⟨x, hx, h⟩
    have fixed := stable bound U.card entries hs (by omega)
    induction h with
    | refl => exact includes edges U.card entries hx
    | tail _ edge ih =>
      change _ ∈ saturate edges U.card entries
      rw [← fixed]
      exact mem_grow.mpr (.inr ⟨_, ih, edge⟩)

end DependencyClosure

open DependencyClosure in
/-- A finite graph of syntactic definition dependencies, with multiple entry names. -/
structure DependencyGraph where
  entries : Finset Var
  nodes : Finset Var
  edges : Finset (Var × Var)
  entries_subset : entries ⊆ nodes
  source_mem : ∀ x y, Edge edges x y → x ∈ nodes
  target_mem : ∀ x y, Edge edges x y → y ∈ nodes

namespace DependencyGraph

abbrev Edge (g : DependencyGraph) := DependencyClosure.Edge g.edges
abbrev Path (g : DependencyGraph) := ReflTransGen g.Edge

private def supportEdges (env : RecEnv schema) (S : Finset Var) : Finset (Var × Var) :=
  S.biUnion fun x => (recursiveVars ((env.lookup x).getD .deadlock)).image (x, ·)

private theorem mem_supportEdges {env : RecEnv schema} {S : Finset Var} {x y : Var} :
    DependencyClosure.Edge (supportEdges env S) x y ↔
      x ∈ S ∧ ∃ b, env.lookup x = some b ∧ y ∈ recursiveVars b := by
  have he : (x, y) ∈ supportEdges env S ↔
      x ∈ S ∧ y ∈ recursiveVars ((env.lookup x).getD .deadlock) := by
    simp [supportEdges, Finset.mem_biUnion, and_assoc]
  change (x, y) ∈ supportEdges env S ↔ _
  rw [he]
  cases h : env.lookup x <;> simp [h]

private theorem support_target {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S) (x y : Var)
    (he : DependencyClosure.Edge (supportEdges env S) x y) : y ∈ S := by
  obtain ⟨hx, b, hb, hy⟩ := mem_supportEdges.mp he
  obtain ⟨c, hc, sub⟩ := hs.2 x hx
  have eq := RecEnv.lookup_unique hb hc
  exact sub (eq ▸ hy)

private theorem supportPath_iff {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S) {y : Var} :
    (∃ x ∈ recursiveVars root, ReflTransGen (DependencyClosure.Edge (supportEdges env S)) x y) ↔
      ReachableVar env root y := by
  constructor
  · rintro ⟨x, hx, path⟩
    induction path with
    | refl => exact .direct hx
    | tail _ he ih =>
      obtain ⟨_, _, hb, hy⟩ := mem_supportEdges.mp he
      exact .throughDefinition ih hb hy
  · intro hy
    induction hy with
    | direct hx => exact ⟨_, hx, .refl⟩
    | throughDefinition source hb hy ih =>
      obtain ⟨x, hx, hp⟩ := ih
      exact ⟨x, hx, hp.tail (mem_supportEdges.mpr
        ⟨reachableVars_subset_of_finiteSupport env root S hs _ source, _, hb, hy⟩)⟩

private def reachable (env : RecEnv schema) (root : DyNetKAT schema) (S : Finset Var) :=
  DependencyClosure.close S (supportEdges env S) (recursiveVars root)

private theorem mem_reachable {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S) {x : Var} :
    x ∈ reachable env root S ↔ ReachableVar env root x :=
  (DependencyClosure.mem_close (support_target hs) hs.1).trans (supportPath_iff hs)

/-- Compute the reachable subgraph of the supplied finite support. -/
def build (env : RecEnv schema) (root : DyNetKAT schema) (S : Finset Var)
    (hs : FiniteSupport env root S) : DependencyGraph :=
  let edges := supportEdges env S
  let nodes := DependencyClosure.close S edges (recursiveVars root)
  { entries := recursiveVars root
    nodes := nodes
    edges := edges.filter fun e => e.1 ∈ nodes
    entries_subset := fun _ hx => (mem_reachable hs).mpr (.direct hx)
    source_mem := fun _ _ he => (Finset.mem_filter.mp he).2
    target_mem := by
      intro x y he
      obtain ⟨he, hx⟩ := Finset.mem_filter.mp he
      obtain ⟨_, _, hb, hy⟩ := mem_supportEdges.mp he
      exact (mem_reachable hs).mpr (.throughDefinition ((mem_reachable hs).mp hx) hb hy) }

theorem mem_build_nodes {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S) {x : Var} :
    x ∈ (build env root S hs).nodes ↔ ReachableVar env root x :=
  mem_reachable hs

theorem build_edge_iff {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S) {x y : Var} :
    (build env root S hs).Edge x y ↔
      ReachableVar env root x ∧ ∃ b, env.lookup x = some b ∧ y ∈ recursiveVars b := by
  change (x, y) ∈ (supportEdges env S).filter _ ↔ _
  rw [Finset.mem_filter]
  change (DependencyClosure.Edge _ x y ∧ x ∈ reachable env root S) ↔ _
  rw [mem_supportEdges, mem_reachable hs]
  exact ⟨fun ⟨⟨_, he⟩, hx⟩ => ⟨hx, he⟩,
    fun ⟨hx, he⟩ => ⟨⟨reachableVars_subset_of_finiteSupport env root S hs x hx, he⟩, hx⟩⟩

theorem reachableVar_iff_entry_path {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S) {y : Var} :
    ReachableVar env root y ↔
      ∃ x ∈ (build env root S hs).entries, (build env root S hs).Path x y := by
  constructor
  · intro hy
    induction hy with
    | direct hx => exact ⟨_, hx, .refl⟩
    | throughDefinition source hb hy ih =>
      obtain ⟨x, hx, path⟩ := ih
      exact ⟨x, hx, path.tail ((build_edge_iff hs).mpr ⟨source, _, hb, hy⟩)⟩
  · rintro ⟨x, hx, h⟩
    induction h with
    | refl => exact .direct hx
    | tail _ edge _ =>
      obtain ⟨hr, _, hb, hy⟩ := (build_edge_iff hs).mp edge
      exact .throughDefinition hr hb hy

/-- All names reachable by zero or more dependency edges from a node. -/
def pathsFrom (g : DependencyGraph) (x : Var) : Finset Var :=
  DependencyClosure.close g.nodes g.edges {x}

theorem mem_pathsFrom {g : DependencyGraph} {x y : Var} (hx : x ∈ g.nodes) :
    y ∈ g.pathsFrom x ↔ g.Path x y := by
  simpa using DependencyClosure.mem_close (entries := {x}) (y := y) g.target_mem
    (Finset.singleton_subset_iff.mpr hx)

theorem path_target {g : DependencyGraph} {x y : Var}
    (hx : x ∈ g.nodes) (h : g.Path x y) : y ∈ g.nodes := by
  cases h with
  | refl => exact hx
  | tail _ he => exact g.target_mem _ _ he

/-- For a reachable name, paths from that name agree with following definitions
from the singleton reference root. -/
theorem path_iff_reachable_from_var {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S) {x y : Var} (hx : ReachableVar env root x) :
    (build env root S hs).Path x y ↔ ReachableVar env (.var x) y := by
  constructor
  · intro path
    induction path with
    | refl => exact .direct (by simp)
    | tail _ edge ih =>
      obtain ⟨_, b, hb, hy⟩ := (build_edge_iff hs).mp edge
      exact .throughDefinition ih hb hy
  · intro reachable
    induction reachable with
    | direct occurs =>
      have eq := Finset.mem_singleton.mp occurs
      cases eq
      exact .refl
    | throughDefinition _ hb hy ih =>
      have source := (mem_build_nodes hs).mp (path_target ((mem_build_nodes hs).mpr hx) ih)
      exact ih.tail ((build_edge_iff hs).mpr ⟨source, _, hb, hy⟩)

/-- Precomputed reachability pairs, shared when constructing the partition. -/
def reachPairs (g : DependencyGraph) : Finset (Var × Var) :=
  g.nodes.biUnion fun x => (g.pathsFrom x).image (x, ·)

theorem mem_reachPairs {g : DependencyGraph} {x y : Var} :
    (x, y) ∈ g.reachPairs ↔ x ∈ g.nodes ∧ g.Path x y := by
  have h : (x, y) ∈ g.reachPairs ↔ x ∈ g.nodes ∧ y ∈ g.pathsFrom x := by
    simp [reachPairs, Finset.mem_biUnion, and_assoc]
  rw [h]
  exact and_congr_right fun hx => mem_pathsFrom hx

private def componentAt (nodes : Finset Var) (paths : Finset (Var × Var)) (x : Var) :
    Finset Var :=
  nodes.filter fun y => (x, y) ∈ paths ∧ (y, x) ∈ paths

def component (g : DependencyGraph) (x : Var) : Finset Var :=
  componentAt g.nodes g.reachPairs x

def sccs (g : DependencyGraph) : Finset (Finset Var) :=
  let paths := g.reachPairs
  g.nodes.image (componentAt g.nodes paths)

theorem mem_component {g : DependencyGraph} {x y : Var} (hx : x ∈ g.nodes) :
    y ∈ g.component x ↔ g.Path x y ∧ g.Path y x := by
  simp only [component, componentAt, Finset.mem_filter, mem_reachPairs]
  exact ⟨fun ⟨_, ⟨_, h₁⟩, _, h₂⟩ => ⟨h₁, h₂⟩,
    fun ⟨h₁, h₂⟩ => ⟨path_target hx h₁, ⟨hx, h₁⟩, path_target hx h₁, h₂⟩⟩

theorem mem_sccs {g : DependencyGraph} {C : Finset Var} :
    C ∈ g.sccs ↔ ∃ x ∈ g.nodes, g.component x = C := Finset.mem_image

theorem component_eq_iff {g : DependencyGraph} {x y : Var}
    (hx : x ∈ g.nodes) (hy : y ∈ g.nodes) :
    g.component x = g.component y ↔ g.Path x y ∧ g.Path y x := by
  constructor
  · intro same
    apply (mem_component hx).mp
    rw [same]
    exact (mem_component hy).mpr ⟨.refl, .refl⟩
  · rintro ⟨hxy, hyx⟩
    ext z
    rw [mem_component hx, mem_component hy]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨hyx.trans h₁, h₂.trans hxy⟩,
      fun ⟨h₁, h₂⟩ => ⟨hxy.trans h₁, h₂.trans hyx⟩⟩

theorem scc_partition {g : DependencyGraph} {x : Var} (hx : x ∈ g.nodes) :
    ∃! C, C ∈ g.sccs ∧ x ∈ C := by
  refine ⟨g.component x, ⟨mem_sccs.mpr ⟨x, hx, rfl⟩,
    (mem_component hx).mpr ⟨.refl, .refl⟩⟩, ?_⟩
  rintro C ⟨hC, h⟩
  obtain ⟨y, hy, rfl⟩ := mem_sccs.mp hC
  exact (component_eq_iff hy hx).mpr ((mem_component hy).mp h)

theorem scc_member_node {g : DependencyGraph} {C : Finset Var}
    (hC : C ∈ g.sccs) {x : Var} (hx : x ∈ C) : x ∈ g.nodes := by
  obtain ⟨y, hy, rfl⟩ := mem_sccs.mp hC
  exact path_target hy ((mem_component hy).mp hx).1

theorem scc_of_member {g : DependencyGraph} {C : Finset Var}
    (hC : C ∈ g.sccs) {x : Var} (hx : x ∈ C) : g.component x = C := by
  obtain ⟨y, hy, rfl⟩ := mem_sccs.mp hC
  obtain ⟨h₁, h₂⟩ := (mem_component hy).mp hx
  exact (component_eq_iff (path_target hy h₁) hy).mpr ⟨h₂, h₁⟩

theorem same_scc_iff {g : DependencyGraph} {C D : Finset Var}
    (hC : C ∈ g.sccs) (hD : D ∈ g.sccs) {x y : Var} (hx : x ∈ C) (hy : y ∈ D) :
    C = D ↔ g.Path x y ∧ g.Path y x := by
  rw [← scc_of_member hC hx, ← scc_of_member hD hy]
  exact component_eq_iff (scc_member_node hC hx) (scc_member_node hD hy)

/-- A cyclic component has multiple members or a self-edge. -/
def isCyclic (g : DependencyGraph) (C : Finset Var) : Bool :=
  decide (1 < C.card) || decide ((C.filter fun x => (x, x) ∈ g.edges).Nonempty)

theorem isCyclic_iff {g : DependencyGraph} {C : Finset Var} :
    g.isCyclic C = true ↔ 1 < C.card ∨ ∃ x ∈ C, g.Edge x x := by
  simp [isCyclic, Finset.Nonempty, Edge, DependencyClosure.Edge]

def cyclicSccs (g : DependencyGraph) : Finset (Finset Var) :=
  g.sccs.filter fun C => g.isCyclic C = true

theorem cyclicSccs_eq_empty_iff (g : DependencyGraph) :
    g.cyclicSccs = ∅ ↔ ∀ C ∈ g.sccs, g.isCyclic C = false := by
  simp [cyclicSccs, Finset.filter_eq_empty_iff]

theorem internal_edge_cyclic {g : DependencyGraph} {C : Finset Var} {x y : Var}
    (hx : x ∈ C) (hy : y ∈ C) (he : g.Edge x y) : g.isCyclic C = true := by
  apply isCyclic_iff.mpr
  by_cases eq : x = y
  · subst y
    exact .inr ⟨x, hx, he⟩
  · exact .inl (Finset.one_lt_card.mpr ⟨x, hx, y, hy, eq⟩)

theorem acyclic_scc_singleton {g : DependencyGraph} {C : Finset Var}
    (hC : C ∈ g.sccs) (acyclic : g.isCyclic C = false) :
    ∃ x, C = {x} ∧ ¬ g.Edge x x := by
  obtain ⟨x, hx, rfl⟩ := mem_sccs.mp hC
  have member := (mem_component hx).mpr ⟨.refl, .refl⟩
  have small : (g.component x).card ≤ 1 := by
    by_contra! h
    exact Bool.noConfusion (acyclic.symm.trans (isCyclic_iff.mpr (.inl h)))
  refine ⟨x, Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr member), ?_⟩
  · intro y hy
    exact Finset.mem_singleton.mpr (Finset.card_le_one_iff.mp small hy member)
  · intro he
    exact Bool.noConfusion (acyclic.symm.trans (internal_edge_cyclic member member he))

theorem cyclic_scc_iff_cycle {g : DependencyGraph} {C : Finset Var} (hC : C ∈ g.sccs) :
    g.isCyclic C = true ↔ ∃ x ∈ C, TransGen g.Edge x x := by
  constructor
  · intro hc
    rcases isCyclic_iff.mp hc with h | ⟨x, hx, edge⟩
    · obtain ⟨x, hx, y, hy, ne⟩ := Finset.one_lt_card.mp h
      obtain ⟨path, back⟩ := (same_scc_iff hC hC hx hy).mp rfl
      cases path with
      | refl => exact (ne rfl).elim
      | tail lead edge => exact ⟨x, hx, (TransGen.tail' lead edge).trans_left back⟩
    · exact ⟨x, hx, .single edge⟩
  · rintro ⟨x, hx, cycle⟩
    obtain ⟨y, edge, back⟩ := TransGen.head'_iff.mp cycle
    have hx' := scc_member_node hC hx
    have hy : y ∈ C := by
      rw [← scc_of_member hC hx]
      exact (mem_component hx').mpr ⟨.single edge, back⟩
    exact internal_edge_cyclic hx hy edge

def condensationEdges (g : DependencyGraph) : Finset (Finset Var × Finset Var) :=
  let paths := g.reachPairs
  let atNode := componentAt g.nodes paths
  (g.edges.image fun e => (atNode e.1, atNode e.2)).filter fun e => e.1 ≠ e.2

theorem condensation_edge_iff {g : DependencyGraph} {C D : Finset Var} :
    (C, D) ∈ g.condensationEdges ↔ C ≠ D ∧
      ∃ x y, g.Edge x y ∧ g.component x = C ∧ g.component y = D := by
  simp only [condensationEdges, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨x, y⟩, h, eq⟩, ne⟩
    have eq' : (g.component x, g.component y) = (C, D) := eq
    exact ⟨ne, x, y, h, congrArg Prod.fst eq', congrArg Prod.snd eq'⟩
  · rintro ⟨ne, x, y, h, rfl, rfl⟩
    exact ⟨⟨(x, y), h, rfl⟩, ne⟩

/-- Rank decreases whenever an edge cannot be followed back to its source. -/
theorem pathsFrom_card_decreases {g : DependencyGraph} {x y : Var}
    (he : g.Edge x y) (noBack : ¬ g.Path y x) :
    (g.pathsFrom y).card < (g.pathsFrom x).card := by
  have hx := g.source_mem x y he
  have hy := g.target_mem x y he
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fun z hz => (mem_pathsFrom hx).mpr ((mem_pathsFrom hy).mp hz |>.head he), ?_⟩
  intro eq
  exact noBack ((mem_pathsFrom hy).mp (eq.symm ▸ (mem_pathsFrom hx).mpr .refl))

/-- The number of nodes reachable from a component, including itself. -/
def componentRank (g : DependencyGraph) (C : Finset Var) : Nat :=
  (DependencyClosure.close g.nodes g.edges C).card

theorem componentRank_eq {g : DependencyGraph} {x : Var} (hx : x ∈ g.nodes) :
    g.componentRank (g.component x) = (g.pathsFrom x).card := by
  unfold componentRank
  congr 1
  ext z
  rw [DependencyClosure.mem_close g.target_mem, mem_pathsFrom hx]
  · constructor
    · rintro ⟨y, hy, path⟩
      exact ((mem_component hx).mp hy).1.trans path
    · intro path
      exact ⟨x, (mem_component hx).mpr ⟨.refl, .refl⟩, path⟩
  · exact fun _ hy => path_target hx ((mem_component hx).mp hy).1

theorem condensation_decreases {g : DependencyGraph} {C D : Finset Var}
    (he : (C, D) ∈ g.condensationEdges) : g.componentRank D < g.componentRank C := by
  obtain ⟨ne, x, y, edge, rfl, rfl⟩ := condensation_edge_iff.mp he
  have hx := g.source_mem x y edge
  have hy := g.target_mem x y edge
  rw [componentRank_eq hx, componentRank_eq hy]
  exact pathsFrom_card_decreases edge (fun back =>
    ne ((component_eq_iff hx hy).mpr ⟨.single edge, back⟩))

/-- Condensation edges, read in the dependency direction, are well founded. -/
theorem condensation_wellFounded (g : DependencyGraph) :
    WellFounded (fun D C => (C, D) ∈ g.condensationEdges) :=
  Subrelation.wf (fun h => condensation_decreases h) (measure g.componentRank).wf

theorem condensation_acyclic (g : DependencyGraph) (C : Finset Var) :
    ¬ TransGen (fun A B => (A, B) ∈ g.condensationEdges) C C := by
  have decreases {A B : Finset Var}
      (h : TransGen (fun A B => (A, B) ∈ g.condensationEdges) A B) :
      g.componentRank B < g.componentRank A := by
    induction h with
    | single he => exact condensation_decreases he
    | tail _ he ih => exact (condensation_decreases he).trans ih
  exact fun h => (Nat.lt_irrefl _) (decreases h)

theorem dependency_decreases {g : DependencyGraph}
    (acyclic : ∀ C ∈ g.sccs, g.isCyclic C = false) {x y : Var} (edge : g.Edge x y) :
    (g.pathsFrom y).card < (g.pathsFrom x).card := by
  have hx := g.source_mem x y edge
  apply pathsFrom_card_decreases edge
  intro back
  have hy := (mem_component hx).mpr ⟨.single edge, back⟩
  have self := (mem_component hx).mpr ⟨.refl, .refl⟩
  exact Bool.noConfusion ((acyclic _ (mem_sccs.mpr ⟨x, hx, rfl⟩)).symm.trans
    (internal_edge_cyclic self hy edge))

theorem dependency_wellFounded (g : DependencyGraph)
    (acyclic : ∀ C ∈ g.sccs, g.isCyclic C = false) :
    WellFounded (fun y x => g.Edge x y) :=
  Subrelation.wf (fun h => dependency_decreases acyclic h)
    (measure fun x => (g.pathsFrom x).card).wf

theorem guarded_scc {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S) (hw : WellFormed env root) {C : Finset Var}
    (hC : C ∈ (build env root S hs).sccs) {x : Var} (hx : x ∈ C) :
    ∃ b, env.lookup x = some b ∧ TypedPaperGuarded b := by
  obtain ⟨b, hb, guard⟩ := hw.2 x ((mem_build_nodes hs).mp (scc_member_node hC hx))
  exact ⟨b, hb, (typedPaperGuarded_iff_guardedOccurrences b).mpr guard⟩

private theorem expand_from_vars (env : RecEnv schema) (p : DyNetKAT schema)
    (expand : ∀ x ∈ recursiveVars p, ∃ q, Ground q ∧ DerivesNoAIP env (.var x) q) :
    ∃ q, Ground q ∧ DerivesNoAIP env p q := by
  induction p with
  | deadlock => exact ⟨.deadlock, rfl, .refl _⟩
  | var x => exact expand x (Finset.mem_singleton_self x)
  | nSeq z p ih =>
    obtain ⟨q, hg, hd⟩ := ih expand
    exact ⟨.nSeq z q, hg, .prefixCongr (.visible (.packet z)) hd⟩
  | recv c z p ih =>
    obtain ⟨q, hg, hd⟩ := ih expand
    exact ⟨.recv c z q, hg, .prefixCongr (.recv c z) hd⟩
  | send c z p ih =>
    obtain ⟨q, hg, hd⟩ := ih expand
    exact ⟨.send c z q, hg, .prefixCongr (.send c z) hd⟩
  | rcfgPrefix c z p ih =>
    obtain ⟨q, hg, hd⟩ := ih expand
    exact ⟨.rcfgPrefix c z q, hg, .prefixCongr (.visible (.rcfg c z)) hd⟩
  | restrict L p ih =>
    obtain ⟨q, hg, hd⟩ := ih expand
    exact ⟨.restrict L q, hg, .restrictCongr L hd⟩
  | project n p ih =>
    obtain ⟨q, hg, hd⟩ := ih expand
    exact ⟨.project n q, hg, .projectCongr n hd⟩
  | choice p q ihp ihq | parallel p q ihp ihq |
      leftMerge p q ihp ihq | commMerge p q ihp ihq =>
    obtain ⟨p', hp, dp⟩ := ihp (fun x hx => expand x (Finset.mem_union_left _ hx))
    obtain ⟨q', hq, dq⟩ := ihq (fun x hx => expand x (Finset.mem_union_right _ hx))
    first
    | exact ⟨.choice p' q', Finset.union_eq_empty.mpr ⟨hp, hq⟩, .choiceCongr dp dq⟩
    | exact ⟨.parallel p' q', Finset.union_eq_empty.mpr ⟨hp, hq⟩, .parallelCongr dp dq⟩
    | exact ⟨.leftMerge p' q', Finset.union_eq_empty.mpr ⟨hp, hq⟩, .leftMergeCongr dp dq⟩
    | exact ⟨.commMerge p' q', Finset.union_eq_empty.mpr ⟨hp, hq⟩, .commMergeCongr dp dq⟩

/-- Acyclic dependencies permit full finite expansion, even under prefixes.
The derivation uses only environment unfolding, congruence, reflexivity and
transitivity. No SOS transitions or guardedness hypothesis are needed. -/
theorem acyclic_unfolds_ground {env : RecEnv schema} {root : DyNetKAT schema} {S : Finset Var}
    (hs : FiniteSupport env root S)
    (acyclic : ∀ C ∈ (build env root S hs).sccs, (build env root S hs).isCyclic C = false) :
    ∃ q, Ground q ∧ DerivesNoAIP env root q := by
  have expansion (x : Var) (hx : ReachableVar env root x) :
      ∃ q, Ground q ∧ DerivesNoAIP env (.var x) q := by
    induction x using (dependency_wellFounded (build env root S hs) acyclic).induction with
    | h x ih =>
      obtain ⟨b, hb, _⟩ := hs.2 x (reachableVars_subset_of_finiteSupport env root S hs x hx)
      obtain ⟨q, hg, hd⟩ := expand_from_vars env b (fun y hy =>
        ih y ((build_edge_iff hs).mpr ⟨hx, b, hb, hy⟩) (.throughDefinition hx hb hy))
      exact ⟨q, hg, .trans (.unfold hb) hd⟩
  exact expand_from_vars env root fun x hx => expansion x (.direct hx)

end DependencyGraph
end DyNetKAT.DyNetKAT
