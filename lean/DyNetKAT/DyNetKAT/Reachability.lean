import DyNetKAT.DyNetKAT.TraceEquations

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

/-- The bound is on the entire source trace, including selected events and
the final packet. None denotes all finite traces. -/
def ReachabilityBudget (bound : Option Nat) (word : List Action) : Prop :=
  match bound with
  | none => True
  | some n => word.length ≤ n

def EndpointReachable {extended : Bool} {env : RecEnv} (p : Program extended env)
    (bound : Option Nat) (stages : List ReconfigSet) (ingress egress : NetKAT) : Prop :=
  flowVia ingress egress fun i o =>
    ∃ word, QueryWord stages i o word ∧ p.Trace word ∧ ReachabilityBudget bound word

theorem TailWord.visible {R : ReconfigSet} {w : List Action} (h : TailWord R w) :
    ∀ a ∈ w, actionAllowed Set.univ a := by
  induction h with
  | last => simp [actionAllowed]
  | packet _ ih => simpa [actionAllowed, List.mem_cons, or_imp, forall_and] using ih
  | rcfg _ _ ih => simpa [actionAllowed, List.mem_cons, or_imp, forall_and] using ih

theorem TailSegments.visible {stages : List ReconfigSet} {w : List Action}
    (h : TailSegments stages w) : ∀ a ∈ w, actionAllowed Set.univ a := by
  induction stages generalizing w with
  | nil => subst w; simp
  | cons R stages ih =>
      obtain ⟨u, v, rfl, word, rest⟩ := h
      exact fun a mem => (List.mem_append.mp mem).elim (word.visible a) (ih rest a)

theorem QueryWord.visible {stages : List ReconfigSet} {i o : CtxPkt} {w : List Action}
    (h : QueryWord stages i o w) : ∀ a ∈ w, actionAllowed Set.univ a := by
  obtain ⟨pre, head, sel, packets, rfl⟩ := h
  intro a mem
  rcases List.mem_append.mp mem with first | last
  · exact sel.visible a first
  · rcases List.mem_append.mp last with before | final
    · have packet := (List.forall_iff_forall_mem.mp packets) a before
      cases a <;> cases packet
      trivial
    · obtain rfl := List.mem_singleton.mp final
      trivial

private theorem corr_graphPath_iff {G : ProcessGraph} {env : RecEnv}
    {q : DyNetKAT} {gp : GProc} (corr : Corr G env q gp) (w : List Action) :
    (∃ dst, GraphPath G gp w dst) ↔ SourceTrace env q w := by
  constructor
  · rintro ⟨dst, path⟩
    unfold GraphPath at path
    obtain ⟨p', path', _⟩ := gsteps_to_steps G env _ _ _ path q corr
    exact ⟨_, _, ⟨p', _, _⟩, path'⟩
  · intro trace
    obtain ⟨p', path⟩ := (sourceTrace_iff_packetLists [] []).mp trace
    obtain ⟨q', path', _⟩ := steps_to_gsteps G env _ _ _ path gp corr
    exact ⟨q', path'⟩

private theorem GraphBisimilarBetween.path_iff {G Q : ProcessGraph} {p q : GProc}
    (h : GraphBisimilarBetween G Q p q) (w : List Action) :
    (∃ dst, GraphPath Q q w dst) ↔ ∃ dst, GraphPath G p w dst := by
  obtain ⟨R, root, fwd, back⟩ := h
  constructor
  · rintro ⟨dst, path⟩
    unfold GraphPath at path
    obtain ⟨d, run, _⟩ := back.traces path p root
    exact ⟨d, run⟩
  · rintro ⟨dst, path⟩
    unfold GraphPath at path
    obtain ⟨d, run, _⟩ := fwd.traces path q root
    exact ⟨d, run⟩

theorem preprocessGraph_bisimilarBetween {G Q : ProcessGraph}
    (h : preprocessGraph G = some Q) :
    GraphBisimilarBetween G Q (.restrict Set.univ G.root) Q.root := by
  let R (p q : GProc) := ∃ u, p = .restrict Set.univ u ∧
    blockCommunication u = some q ∧ gprocRefs u ⊆ G.nodes
  refine ⟨R, ⟨G.root, rfl, (preprocessGraph_eq_some h).2.1, G.root_closed⟩, ?_, ?_⟩
  · rintro _ q ⟨p, rfl, prep, closed⟩ pt hl a dst pt' hl' step
    cases step with
    | restrict _ _ u _ _ _ _ _ allowed inner =>
        obtain ⟨t, eq, hc, hs⟩ :=
          (preprocessGraph_bisimulation h prep closed pt hl pt' hl' a).1 u
            (.restrict _ _ _ _ _ _ _ _ allowed inner)
        exact ⟨t, hs, u, rfl, eq, hc⟩
  · rintro q _ ⟨p, rfl, prep, closed⟩ pt hl a dst pt' hl' step
    obtain ⟨u, eq, hc, hs⟩ :=
      (preprocessGraph_bisimulation h prep closed pt hl pt' hl' a).2 dst step
    exact ⟨.restrict Set.univ u, hs, u, rfl, eq, hc⟩

/-- Eq. (34) uses an empty list of tail stages. Eq. (35) uses one stage.
Multiple stages apply the existing structural tail in order. -/
def graphReachability (G : ProcessGraph) (stages : List ReconfigSet)
    (ingress egress : NetKAT) : Option Bool := do
  let tail ← graphTails G stages
  let head ← graphHead tail
  return !netkatIsZero (reachabilityPolicy ingress head egress)

theorem graphReachability_correct {G : ProcessGraph} (ready : TraceReady G)
    (stages : List ReconfigSet) (ingress egress : NetKAT) :
    graphReachability G stages ingress egress = some true ↔ flowVia ingress egress
      (fun i o => ∃ w dst, QueryWord stages i o w ∧ GraphPath G G.root w dst) := by
  obtain ⟨Q, H, tails, head⟩ := graphTails_head_exists ready stages
  change ((graphTails G stages).bind fun Q => (graphHead Q).bind fun H =>
    some (!netkatIsZero (reachabilityPolicy ingress H egress))) = some true ↔ _
  rw [tails, Option.some_bind, head, Option.some_bind]
  simpa only [Option.some.injEq, Bool.not_eq_true', flowVia,
    ← graphTails_head_iff ready tails head] using netkatIsZero_reachabilityPolicy_false_iff ingress H egress

private theorem endpoint_lift {extended : Bool} {env : RecEnv} {p : Program extended env}
    {G : ProcessGraph} {stages : List ReconfigSet} {bound : Option Nat} (ready : TraceReady G)
    (view : ∀ w i o, QueryWord stages i o w →
      ((∃ dst, GraphPath G G.root w dst) ↔ p.Trace w ∧ ReachabilityBudget bound w))
    (ingress egress : NetKAT) :
    graphReachability G stages ingress egress = some true ↔
      EndpointReachable p bound stages ingress egress := by
  rw [graphReachability_correct ready]
  unfold flowVia EndpointReachable
  constructor
  · rintro ⟨s, i, o, t, ins, ⟨w, dst, word, path⟩, outs⟩
    exact ⟨s, i, o, t, ins, ⟨w, word, (view w i o word).mp ⟨dst, path⟩⟩, outs⟩
  · rintro ⟨s, i, o, t, ins, ⟨w, word, trace, bound⟩, outs⟩
    obtain ⟨dst, path⟩ := (view w i o word).mpr ⟨trace, bound⟩
    exact ⟨s, i, o, t, ins, ⟨w, dst, word, path⟩, outs⟩

/-- Exact source counterpart of the successive tail graphs. A nonempty
suffix selects a continuation, and each removed segment accounts for its
actual source actions before that suffix. -/
theorem graphTails_source_iff {extended : Bool} {env : RecEnv} {p : Program extended env}
    (compiled : p.Compiled) {G Q : ProcessGraph} (prep : preprocessGraph compiled.graph = some G)
    {stages : List ReconfigSet} (tails : graphTails G stages = some Q) {w : List Action}
    (nonempty : w ≠ []) :
    (∃ dst, GraphPath Q Q.root w dst) ↔
      ∃ pre, TailSegments stages pre ∧ p.Trace (pre ++ w) ∧ ∀ a ∈ w, actionAllowed Set.univ a := by
  have exactTail (dst : GProc) :=
    graphTails_feasible_iff (dst := dst) (preprocessGraph_traceReady prep) tails nonempty
  have view (t : List Action) : (∃ dst, GraphPath G G.root t dst) ↔
      p.Trace t ∧ ∀ a ∈ t, actionAllowed Set.univ a := by
    rw [(preprocessGraph_bisimilarBetween prep).path_iff,
      corr_graphPath_iff (corr_restrict_intro (L := Set.univ) compiled.corr),
      sourceTrace_restrict_iff]
    rfl
  constructor
  · rintro ⟨dst, run⟩
    obtain ⟨pre, segments, full⟩ := (exactTail dst).mp run
    obtain ⟨source, visible⟩ := (view _).mp ⟨dst, full⟩
    exact ⟨pre, segments, source, fun a mem => visible a (List.mem_append_right _ mem)⟩
  · rintro ⟨pre, segments, source, visible⟩
    obtain ⟨dst, run⟩ := (view _).mpr ⟨source, fun a mem =>
      (List.mem_append.mp mem).elim (segments.visible a) (visible a)⟩
    exact ⟨dst, (exactTail dst).mpr ⟨pre, segments, run⟩⟩

theorem graphHead_source_iff {extended : Bool} {env : RecEnv} {p : Program extended env}
    (compiled : p.Compiled) {G : ProcessGraph} (prep : preprocessGraph compiled.graph = some G)
    {Q : ProcessGraph} {stages : List ReconfigSet} (tails : graphTails G stages = some Q)
    {H : NetKAT} (head : graphHead Q = some H) (i o : CtxPkt) :
    Semantics H i o ↔ ∃ w, QueryWord stages i o w ∧ p.Trace w := by
  rw [graphTails_head_iff (preprocessGraph_traceReady prep) tails head]
  have view (w : List Action) (query : QueryWord stages i o w) :
      (∃ dst, GraphPath G G.root w dst) ↔ p.Trace w := by
    rw [(preprocessGraph_bisimilarBetween prep).path_iff,
      corr_graphPath_iff (corr_restrict_intro (L := Set.univ) compiled.corr),
      sourceTrace_restrict_iff]
    exact ⟨And.left, fun run => ⟨run, query.visible⟩⟩
  constructor
  · rintro ⟨w, dst, query, path⟩
    exact ⟨w, query, (view w query).mp ⟨dst, path⟩⟩
  · rintro ⟨w, query, trace⟩
    obtain ⟨dst, path⟩ := (view w query).mpr trace
    exact ⟨w, dst, query, path⟩

/-- The existing two-verdict API on sequential graphs reports source
isolation (34) and source forwarding after a selected event (35). -/
theorem compiledSafety_source_correct {extended : Bool} {env : RecEnv} {p : Program extended env}
    (compiled : p.Compiled) {G : ProcessGraph} (prep : preprocessGraph compiled.graph = some G)
    (R : ReconfigSet) (ingress egress : NetKAT) :
    ((compiled.safety R ingress egress).initialCondition = .isZero true ↔
      ¬ EndpointReachable p none [] ingress egress) ∧
    ((compiled.safety R ingress egress).postReconfigurationCondition = .nonzero true ↔
      EndpointReachable p none [R] ingress egress) := by
  obtain ⟨initial, post⟩ := compiled.safety_correct prep R ingress egress
  obtain ⟨H, head⟩ := graphHead_supported_some G (preprocessGraph_supported prep).1
  obtain ⟨Q, tail⟩ := graphTail_supported_some (R := R) (preprocessGraph_supported prep).2
  obtain ⟨H', head'⟩ := graphTail_head_some tail
  have empty : graphTails G [] = some G := rfl
  have single : graphTails G [R] = some Q := Option.bind_eq_some_iff.mpr ⟨Q, tail, rfl⟩
  constructor
  · rw [initial]
    have spec (i o : CtxPkt) : GraphHeadSpec G G.root i o ↔ Semantics H i o :=
      ⟨graphHead_complete G H head i o, graphHead_sound G H head i o⟩
    simp only [EndpointReachable, ReachabilityBudget, and_true, flowVia, spec,
      ← graphHead_source_iff compiled prep empty head]
  · rw [post]
    have spec (i o : CtxPkt) : GraphTailSpec G R G.root i o ↔ Semantics H' i o :=
      ⟨graphTail_complete tail head', graphTail_sound tail head'⟩
    simp only [EndpointReachable, ReachabilityBudget, and_true, flowVia, spec,
      ← graphHead_source_iff compiled prep single head']

theorem normalizedReachability_correct {extended : Bool} {env : RecEnv}
    {p : Program extended env} (compiled : p.Compiled) {n : Nat}
    {C : NormalizationCandidate n} (exactRows : NormalizationExact compiled.graph C)
    (stages : List ReconfigSet) (ingress egress : NetKAT) :
    graphReachability (normalizeCertifiedGraph C exactRows) stages ingress egress = some true ↔
      EndpointReachable p none stages ingress egress := by
  apply endpoint_lift (normalizeCertifiedGraph_traceReady exactRows) _ ingress egress
  intro w i o query
  rw [(normalizeCertifiedGraph_correct exactRows).2.1.path_iff,
    corr_graphPath_iff (corr_restrict_intro (L := Set.univ) compiled.corr), sourceTrace_restrict_iff]
  exact ⟨fun h => ⟨h.1, trivial⟩, fun h => ⟨h.1, query.visible⟩⟩

/-- The static §V endpoint formula is existential over the NetKAT
composition, including the zero-iteration case of star. -/
theorem staticReachability_iff (ingress policy topology egress : NetKAT) :
    netkatIsZero (reachabilityPolicy ingress (.star (.seq policy topology)) egress) = false ↔
      flowVia ingress egress (Semantics (.star (.seq policy topology))) :=
  netkatIsZero_reachabilityPolicy_false_iff ..


private theorem projectionSupportEmpty {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {n : Nat} {state : CheckedResidual} {q : DyNetKAT}
    (render : renderProjection G bodyChecks n state = some q) (env : RecEnv) :
    FiniteSupport env q ∅ :=
  ⟨by rw [renderProjection_closed render], by simp⟩

/-- The existing finite projection supplies the structural graph. Pruning
unavailable prefixes after rendering is exact under the outer restriction. -/
def projectedReachability {extended : Bool} {env : RecEnv} {p : Program extended env}
    (compiled : p.Compiled) (rootChecks : RestrictionChecks)
    (bodyChecks : NodeId → RestrictionChecks) (n : Nat)
    (stages : List ReconfigSet) (ingress egress : NetKAT) : Option Bool :=
  match h : renderProjection compiled.graph bodyChecks n (compiled.initial rootChecks).checked with
  | none => none
  | some q => (preprocessGraph (toGraph env q ∅ (projectionSupportEmpty h env))).bind
      (fun G => graphReachability G stages ingress egress)

theorem projectedReachability_correct {extended : Bool} {env : RecEnv}
    {p : Program extended env} (compiled : p.Compiled) (rootChecks : RestrictionChecks)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : (compiled.initial rootChecks).checked.Valid live) (n : Nat)
    (stages : List ReconfigSet) (ingress egress : NetKAT) :
    projectedReachability compiled rootChecks bodyChecks n stages ingress egress = some true ↔
      EndpointReachable p (some n) stages ingress egress := by
  obtain ⟨q, render⟩ := renderProjection_exists support n valid
  let T := toGraph env q ∅ (projectionSupportEmpty render env)
  have root : (blockCommunication T.root).isSome := renderProjection_preprocessable render
  have labels : ∀ i ∈ T.nodes, (blockCommunication (T.label i)).isSome := by
    intro i mem
    simp [T, toGraph] at mem
  obtain ⟨Q, prep⟩ := preprocessGraph_exists root labels
  have hB := renderProjection_bisimilar support valid compiled.corr render
  have corr : Corr T env q T.root := toGraph_corr env q ∅ (projectionSupportEmpty render env)
  unfold projectedReachability
  split
  · rename_i missing
    rw [render] at missing
    contradiction
  · rename_i q' result
    have eq := Option.some.inj (render.symm.trans result)
    subst q'
    change (preprocessGraph T).bind (fun G => graphReachability G stages ingress egress) = some true ↔ _
    rw [prep, Option.some_bind]
    apply endpoint_lift (preprocessGraph_traceReady prep) _ ingress egress
    intro w i o query
    rw [(preprocessGraph_bisimilarBetween prep).path_iff,
      corr_graphPath_iff (corr_restrict_intro (L := Set.univ) corr),
      sourceTrace_restrict_iff, hB.sourceTrace_iff, sourceTrace_project_iff]
    exact ⟨And.left, fun run => ⟨run, query.visible⟩⟩

end DyNetKAT.DyNetKAT
