import DyNetKAT.NetKAT.SymbolicDerives
import DyNetKAT.Frontend.V11Reachability

namespace DyNetKAT.Frontend.V11

open _root_.DyNetKAT.NetKAT _root_.DyNetKAT.DyNetKAT

private def merge {s : PacketSchema} (p q : NetKAT s) : NetKAT s :=
  if p = .drop then q else if q = .drop ∨ p = q then p else .union p q

private theorem merge_correct {s : PacketSchema} (p q : NetKAT s) (i o : s.Packet) :
    Semantics (merge p q) i o ↔ Semantics p i o ∨ Semantics q i o := by
  unfold merge
  split
  · rename_i h; subst p; simp [Semantics]
  · split
    · rename_i h
      rcases h with h | h
      · subst q; simp [Semantics]
      · subst q; simp
    · rfl

private def removeEmptyBranches {s : PacketSchema} : NetKAT s → NetKAT s
  | .union p q => merge (removeEmptyBranches p) (removeEmptyBranches q)
  | p => p

private theorem removeEmptyBranches_correct {s : PacketSchema} (p : NetKAT s) (i o : s.Packet) :
    Semantics (removeEmptyBranches p) i o ↔ Semantics p i o := by
  induction p <;> try rfl
  case union p q hp hq =>
    exact (merge_correct ..).trans (or_congr hp hq)

private def unionPolicies {s : PacketSchema} : List (NetKAT s) → NetKAT s
  | [] => .drop
  | p :: ps => merge p (unionPolicies ps)

private theorem unionPolicies_correct {s : PacketSchema} (ps : List (NetKAT s)) (i o : s.Packet) :
    Semantics (unionPolicies ps) i o ↔ ∃ n ∈ ps, Semantics n i o := by
  induction ps with
  | nil => simp [unionPolicies, Semantics]
  | cons p ps ih => rw [unionPolicies, merge_correct, ih]; simp

def stagesOf {s : PacketSchema} (stages : List (List (Reconfiguration s))) :
    List (ReconfigSet s) :=
  stages.map fun stage => (stage.map fun event => (event.channel, event.payload)).toFinset

def SelectedHead (job : Loaded) (depth : Nat) (stages : List (ReconfigSet job.domains.schema)) :=
  { n : NetKAT job.domains.schema // ∀ i o,
    Semantics n i o ↔ ∃ word, QueryWord stages i o word ∧ job.program.Trace word ∧
      word.length ≤ depth }

def selectHead (job : Loaded) (prepared : Prepared job) (depth : Nat)
    (stages : List (ReconfigSet job.domains.schema)) : Except String (SelectedHead job depth stages) := do
  if h : depth = stages.length + 1 then
    let ns := tightHead job.support prepared.rootChecks prepared.support prepared.valid stages
    return ⟨unionPolicies ns.val, fun i o =>
      (unionPolicies_correct ..).trans (by rw [h]; exact ns.property i o)⟩
  -- Retain the success equation for the projection's trace certificate.
  match hp : renderProjection job.support.graph prepared.bodyChecks depth
      (job.support.initial prepared.rootChecks).checked with
  | none => throw "could not render bounded projection"
  | some p =>
    let env := fun name => job.definitions.lookup name
    let support := projectionSupportEmpty hp env
    let G := toGraph env p ∅ support
    match prep : preprocessGraph G with
    | none => throw "could not prepare projected graph"
    | some Q =>
      match tails : graphTails Q stages with
      | none => throw "could not extract nested tail"
      | some T =>
        match head : graphHead T with
        | none => throw "could not extract head"
        | some n =>
          return ⟨removeEmptyBranches n, by
            intro i o
            rw [removeEmptyBranches_correct, graphTails_head_iff (preprocessGraph_traceReady prep) tails head]
            have view (w : List (Action job.domains.schema)) (query : QueryWord stages i o w) :
                (∃ dst, GraphPath Q Q.root w dst) ↔ job.program.Trace w ∧ w.length ≤ depth := by
              have corr := toGraph_corr env p ∅ support
              have bis := renderProjection_bisimilar prepared.support prepared.valid job.support.corr hp
              rw [(preprocessGraph_bisimilarBetween prep).path_iff]
              change (∃ dst, GraphPath (toGraph env p ∅ support) (.restrict Set.univ (toGProc p)) w dst) ↔ _
              rw [corr_graphPath_iff (corr_restrict_intro (L := Set.univ) corr),
                sourceTrace_restrict_iff, bis.sourceTrace_iff, sourceTrace_project_iff]
              exact ⟨And.left, fun run => ⟨run, query.visible⟩⟩
            exact ⟨fun ⟨w,dst,query,path⟩ => ⟨w,query,(view w query).mp ⟨dst,path⟩⟩,
              fun ⟨w,query,tr⟩ => let ⟨dst,path⟩ := (view w query).mpr tr; ⟨w,dst,query,path⟩⟩⟩

private def containsStar {s : PacketSchema} : NetKAT s → Bool
  | .star _ => true
  | .union p q | .seq p q => containsStar p || containsStar q
  | _ => false

def waypointRelation {s : PacketSchema} (n : NetKAT s) (ing out via : Predicate s) :
    Except String (NetKAT s) := do
  let (before, after) ← match n with
    | .star h => pure (.star (.seq (.test (.pNot out)) h), .star (.seq (.test (.pNot ing)) h))
    | h =>
        if containsStar h then throw "waypoint requires an outermost star or a star-free selected head"
        else pure (.seq (.test (.pNot out)) h, .seq (.test (.pNot ing)) h)
  return .seq (.test ing) (.seq before (.seq (.test via) (.seq after (.test out))))

def checkInclusion {s : PacketSchema} (a b : NetKAT s) :
    { result : Bool // result = true ↔ ∀ i o, Semantics a i o → Semantics b i o } :=
  ⟨netkatNativeEquivFinite (.union a b) b, by
    rw [netkatNativeEquivFinite_correct]
    exact ⟨fun h i o ha => (h i o).mp (Or.inl ha),
      fun h i o => ⟨fun hab => hab.elim (h i o) id, Or.inr⟩⟩⟩

/-- Exact inclusion after fixing the input packet. This specializes the
native relation check using the verified supplied-packet evaluator. -/
private def includedAt {s : PacketSchema} (a b : NetKAT s) (i : s.Packet) :
    { result : Bool // result = true ↔ ∀ o, Semantics a i o → Semantics b i o } := by
  letI := s.packetEq
  match ha : execute a i, hb : execute b i with
  | .supported sa, .supported sb =>
    refine ⟨decide (sa ⊆ sb), ?_⟩
    obtain ⟨aa, ha', ah⟩ := execute_correct a i
    obtain ⟨bb, hb', bh⟩ := execute_correct b i
    rw [ha] at ha'; rw [hb] at hb'
    cases ha'; cases hb'
    simp only [decide_eq_true_eq]
    exact ⟨fun sub o h => (bh o).mpr (sub ((ah o).mp h)),
      fun sub o h => (bh o).mp (sub o ((ah o).mpr h))⟩
  | .unsupported, _ =>
    exfalso
    obtain ⟨_, h, _⟩ := execute_correct a i
    rw [ha] at h
    contradiction
  | _, .unsupported =>
    exfalso
    obtain ⟨_, h, _⟩ := execute_correct b i
    rw [hb] at h
    contradiction

private def slice {s : PacketSchema} (ing : Predicate s) (f : s.Field) (v : s.Value f) :=
  pinnedIngress (.pAnd ing (.pFieldEq ⟨f, v⟩))

/-- Cover the ingress relation by pinning a single additional field.
The coverage check traverses field values, with the other fields fixed. -/
private def inclusionByField {s : PacketSchema} (f : s.Field) (ing out : Predicate s)
    (n b : NetKAT s) :
    Option { result : Bool // result = true ↔ ∀ i o,
      Semantics (reachabilityPolicy (.test ing) n (.test out)) i o → Semantics b i o } := by
  letI := s.valueFinite f
  let a := reachabilityPolicy (.test ing) n (.test out)
  if h : ∀ v, (slice ing f v).isSome then
    let candidate := fun v => ((slice ing f v).get (h v))
    refine some ⟨decide (∀ v, (includedAt a b (candidate v).val).val = true), ?_⟩
    simp only [decide_eq_true_eq]
    constructor
    · intro ok i o sem
      have hi : ing.holds i := by
        obtain ⟨j, hi, _⟩ := (seq_sem ..).mp sem
        exact hi.1
      have eq := (candidate (i f)).property i (by
        change (ing.eval i && (Predicate.pFieldEq ⟨f, i f⟩).eval i) = true
        apply Bool.and_eq_true_iff.mpr
        refine ⟨hi, ?_⟩
        simp [Predicate.eval])
      have result := ((includedAt a b (candidate (i f)).val).property.mp (ok (i f))) o (eq ▸ sem)
      exact eq.symm ▸ result
    · intro ok v
      exact (includedAt a b (candidate v).val).property.mpr (ok _)
  else
    exact none

def checkWaypointInclusion {s : PacketSchema} (fields : List s.Field)
    (ing out : Predicate s) (n b : NetKAT s) :
    { result : Bool // result = true ↔ ∀ i o,
      Semantics (reachabilityPolicy (.test ing) n (.test out)) i o → Semantics b i o } :=
  let fiber := if fields.length < 2 then none
    else fields.findSome? (fun f => inclusionByField f ing out n b)
  match fiber with
  | some answer => answer
  | none => checkInclusion (reachabilityPolicy (.test ing) n (.test out)) b

theorem checkWaypointInclusion_eq_symbolic {s : PacketSchema} (fields : List s.Field)
    (ing out : Predicate s) (n b : NetKAT s) :
    (checkWaypointInclusion fields ing out n b).val =
      netkatNativeEquivFinite (.union (reachabilityPolicy (.test ing) n (.test out)) b) b :=
  Bool.eq_iff_iff.mpr ((checkWaypointInclusion fields ing out n b).property.trans
    (checkInclusion (reachabilityPolicy (.test ing) n (.test out)) b).property.symm)

theorem checkWaypointInclusion_iff_derives {s : PacketSchema} (fields : List s.Field)
    (ing out : Predicate s) (n b : NetKAT s) :
    (checkWaypointInclusion fields ing out n b).val = true ↔
      Derives (.union (reachabilityPolicy (.test ing) n (.test out)) b) b := by
  rw [checkWaypointInclusion_eq_symbolic, netkatNativeEquivFinite_iff_derives]

end DyNetKAT.Frontend.V11
