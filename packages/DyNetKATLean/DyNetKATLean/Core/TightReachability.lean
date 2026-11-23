import DyNetKATLean.Core.TraceSafetyCheck
import DyNetKATLean.Core.Reachability

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT
variable {s : PacketSchema}

/-- Extract a required value from a conjunctive ingress test. -/
private def pinned (f : s.Field) : Predicate s → Option (s.Value f)
  | .pFieldEq e =>
      letI := s.fieldEq
      if h : e.field = f then some (h ▸ e.value) else none
  | .pAnd p q => (pinned f p).or (pinned f q)
  | _ => none

private theorem pinned_correct (f : s.Field) (p : Predicate s) (i : s.Packet)
    (hp : p.holds i) {v} (found : pinned f p = some v) : i f = v := by
  induction p with
  | pFieldEq e =>
      cases e with
      | mk field value =>
        simp only [pinned] at found
        split at found
        · next h =>
          subst field
          simp at found
          subst v
          letI := s.valueEq f
          exact of_decide_eq_true hp
        · contradiction
  | pAnd p q ihp ihq =>
      obtain ⟨a, b⟩ := Bool.and_eq_true_iff.mp hp
      simp only [pinned] at found
      cases h : pinned f p with
      | none => exact ihq b (by simpa [h] using found)
      | some u => have e := Option.some.inj (by simpa [h] using found : some u = some v)
                  exact ihp a (h.trans (congrArg some e))
  | _ => contradiction

def pinnedIngress (p : Predicate s) : Option { i : s.Packet // ∀ j, p.holds j → j = i } :=
  letI := s.fieldFinite
  if h : ∀ f, (pinned f p).isSome then
    some ⟨fun f => (pinned f p).get (h f), fun j hj =>
      funext fun f => pinned_correct f p j hj (Option.some_get (h f)).symm⟩
  else none

private def OnePerStage : List (ReconfigSet s) → List (Action s) → Prop
  | [], w => w = []
  | r :: rs, a :: w => SelectedReconfig r a ∧ OnePerStage rs w
  | _ :: _, [] => False

private theorem segments_length {rs : List (ReconfigSet s)} {w : List (Action s)}
    (h : TailSegments rs w) : rs.length ≤ w.length := by
  induction rs generalizing w with
  | nil => simp
  | cons r rs ih =>
      obtain ⟨u,v,rfl,hu,hv⟩ := h
      have a := List.length_pos_iff.mpr hu.nonempty
      have b := ih hv
      simp only [List.length_append, List.length_cons]
      omega

private theorem segments_tight {rs : List (ReconfigSet s)} {w : List (Action s)}
    (h : TailSegments rs w) (len : w.length ≤ rs.length) : OnePerStage rs w := by
  induction rs generalizing w with
  | nil => exact h
  | cons r rs ih =>
      obtain ⟨u,v,rfl,hu,hv⟩ := h
      have a := List.length_pos_iff.mpr hu.nonempty
      have b := segments_length hv
      simp only [List.length_append, List.length_cons] at len
      cases hu with
      | last mem => exact ⟨mem, ih hv (by simpa only [List.length_singleton, Nat.add_comm 1, Nat.add_le_add_iff_right] using len)⟩
      | packet hu | rcfg _ hu =>
        have := List.length_pos_iff.mpr hu.nonempty
        simp at a len
        omega

private theorem one_segments {rs : List (ReconfigSet s)} {w : List (Action s)}
    (h : OnePerStage rs w) : TailSegments rs w ∧ w.length = rs.length := by
  induction rs generalizing w with
  | nil => have e : w = [] := h; subst w; exact ⟨rfl,rfl⟩
  | cons r rs ih =>
      cases w with
      | nil => contradiction
      | cons a w =>
        obtain ⟨mem,rest⟩ := h
        obtain ⟨seg,len⟩ := ih rest
        cases a with
        | rcfg x n => exact ⟨⟨[_],w,rfl,.last mem,seg⟩, by simp [len]⟩
        | _ => contradiction

private def TightTrace (env : RecEnv s) (p : DyNetKAT s) (rs : List (ReconfigSet s))
    (i : s.Packet) (out : Predicate s) : Prop :=
  ∃ pre o, OnePerStage rs pre ∧ out.holds o ∧ SourceTrace env p (pre ++ [.packet i o])

private theorem tight_iff {env : RecEnv s} {p : Program true env}
    {rs : List (ReconfigSet s)} {ing out : Predicate s} {i : s.Packet}
    (unique : ∀ j, ing.holds j → j = i) :
    EndpointReachable p (some (rs.length + 1)) rs (.test ing) (.test out) ↔
      ing.holds i ∧ TightTrace env p.term rs i out := by
  constructor
  · rintro ⟨_, a, b, _, hi, ⟨w, ⟨pre, head, seg, _, rfl⟩, trace, budget⟩, ho⟩
    change ing.holds _ ∧ _ at hi
    change out.holds _ ∧ _ at ho
    obtain ⟨hi, rfl⟩ := hi
    have lower := segments_length seg
    simp [ReachabilityBudget] at budget
    have empty : head = [] := List.length_eq_zero_iff.mp (by omega)
    subst head
    obtain rfl := unique _ hi
    exact ⟨hi, pre, b, segments_tight seg (by omega), ho.1, by simpa using trace⟩
  · rintro ⟨hi, pre, o, sel, ho, trace⟩
    obtain ⟨seg,len⟩ := one_segments sel
    have word : QueryWord rs i o (pre ++ [.packet i o]) :=
      ⟨pre, [], seg, by simp, rfl⟩
    refine ⟨i, i, o, o, ⟨hi,rfl⟩, ?_, ⟨ho,rfl⟩⟩
    refine ⟨pre ++ [Action.packet i o], word, ?_, ?_⟩
    · exact trace
    · simp [ReachabilityBudget, len]

private def packetOut (i : s.Packet) (out : Predicate s) (l : MoveLabel s) : Bool :=
  match l with
  | .visible (.packet n) =>
      match execute n i with
      | .supported outputs => decide (∃ o ∈ outputs, out.eval o = true)
      | .unsupported => false
  | _ => false

private theorem packetOut_iff (i : s.Packet) (out : Predicate s) (l : MoveLabel s) :
    packetOut i out l = true ↔ ∃ o, out.holds o ∧ l.Realizes [i] [] (.packet i o) [] [o] := by
  cases l with
  | visible a =>
    cases a with
    | packet n =>
      obtain ⟨outputs, eval, exactOutput⟩ := execute_correct n i
      simp only [packetOut, eval, decide_eq_true_eq]
      constructor
      · rintro ⟨o, mem, ho⟩
        exact ⟨o, ho, .packet ((historySemantics_singleton_iff_packetSemantics ..).mpr
          ((exactOutput o).mpr mem))⟩
      · rintro ⟨o, ho, step⟩
        cases step with
        | packet history => exact ⟨o, (exactOutput o).mp
            ((historySemantics_singleton_iff_packetSemantics ..).mp history), ho⟩
    | rcfg => exact ⟨Bool.noConfusion, fun ⟨_, _, h⟩ => by cases h⟩
  | recv | send => exact ⟨Bool.noConfusion, fun ⟨_, _, h⟩ => by cases h⟩

private def eventOf (r : ReconfigSet s) (l : MoveLabel s) : Option (Action s) :=
  match l with
  | .visible (.rcfg x n) => if (x,n) ∈ r then some (.rcfg x n) else none
  | _ => none

private theorem eventOf_iff (r : ReconfigSet s) (l : MoveLabel s) (a : Action s) :
    eventOf r l = some a ↔ SelectedReconfig r a ∧ l.Realizes (a.pendingFor []) [] a [] (a.handledAfter []) := by
  constructor
  · intro h
    cases l with
    | recv | send => contradiction
    | visible v =>
      cases v with
      | packet => contradiction
      | rcfg x n =>
        by_cases mem : (x,n) ∈ r
        · have eq : Action.rcfg x n = a := Option.some.inj (by simpa [eventOf, mem] using h)
          subst a
          exact ⟨mem,.rcfg⟩
        · simp [eventOf, mem] at h
  · rintro ⟨selected,step⟩
    cases a with
    | rcfg x n => cases step; simp [eventOf, show (x,n) ∈ r from selected]
    | _ => contradiction

private def search {G : ProcessGraph s} {bodyChecks live}
    (support : ProjectionSupport G bodyChecks live) (state : CheckedResidual s)
    (valid : state.Valid live) (i : s.Packet) (out : Predicate s) :
    List (ReconfigSet s) → Bool
  | [] =>
    (TraceSafety.checkedRow support state valid).val.any fun m => packetOut i out m.1
  | r :: rs =>
    let row := TraceSafety.checkedRow support state valid
    row.val.attach.any fun m => (eventOf r m.val.1).isSome &&
      search support m.val.2 (row.property.2 _ m.property) i out rs

private theorem search_correct {G : ProcessGraph s} {bodyChecks live}
    (support : ProjectionSupport G bodyChecks live) {env : RecEnv s} {p : DyNetKAT s}
    {state : CheckedResidual s} (valid : state.Valid live) (corr : Corr G env p state.proc)
    (i : s.Packet) (out : Predicate s) (rs : List (ReconfigSet s)) :
    search support state valid i out rs = true ↔ TightTrace env p rs i out := by
  induction rs generalizing p state with
  | nil =>
    let row := TraceSafety.checkedRow support state valid
    change row.val.any (fun m => packetOut i out m.1) = true ↔ _
    simp only [List.any_eq_true, TightTrace, OnePerStage]
    constructor
    · rintro ⟨m, mem, found⟩
      obtain ⟨o, ho, realized⟩ := (packetOut_iff ..).mp found
      obtain ⟨q, step, _⟩ := (row.property.1.source_steps corr [i] [] (.packet i o) [] [o]).1
        m.1 m.2.proc (List.mem_map.mpr ⟨m,mem,rfl⟩) realized
      exact ⟨[],o,rfl,ho,sourceTrace_cons_actionStep.mpr ⟨q,step,sourceTrace_nil ..⟩⟩
    · rintro ⟨_,o,rfl,ho,tr⟩
      obtain ⟨q, step, _⟩ := sourceTrace_cons_actionStep.mp tr
      obtain ⟨l, target, mem, realized, _⟩ :=
        (row.property.1.source_steps corr [i] [] (.packet i o) [] [o]).2 q step
      obtain ⟨m, hm, eq⟩ := List.mem_map.mp mem
      have same : m.1 = l := congrArg Prod.fst eq
      exact ⟨m,hm,(packetOut_iff ..).mpr ⟨o,ho,same.symm ▸ realized⟩⟩
  | cons r rs ih =>
    let row := TraceSafety.checkedRow support state valid
    unfold search
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨m, mem⟩, _, selected, next⟩
      obtain ⟨a, he⟩ := Option.isSome_iff_exists.mp selected
      obtain ⟨ha, realized⟩ := (eventOf_iff ..).mp he
      obtain ⟨q, step, hc⟩ :=
        (row.property.1.source_steps corr (a.pendingFor []) [] a [] (a.handledAfter [])).1
          m.1 m.2.proc (List.mem_map.mpr ⟨m,mem,rfl⟩) realized
      obtain ⟨pre,o,hpre,ho,tr⟩ := (ih (row.property.2 m mem) hc).mp next
      exact ⟨a::pre,o,⟨ha,hpre⟩,ho,sourceTrace_cons_actionStep.mpr ⟨q,step,tr⟩⟩
    · rintro ⟨pre,o,hpre,ho,tr⟩
      cases pre with
      | nil => contradiction
      | cons a pre =>
        obtain ⟨ha,hpre⟩ := hpre
        obtain ⟨q,step,rest⟩ := sourceTrace_cons_actionStep.mp tr
        obtain ⟨l,target,mem,realized,hc⟩ :=
          (row.property.1.source_steps corr (a.pendingFor []) [] a [] (a.handledAfter [])).2 q step
        obtain ⟨m, hm, eq⟩ := List.mem_map.mp mem
        cases m with
        | mk label next =>
          cases eq
          exact ⟨⟨(label,next),hm⟩,by simp,
            Option.isSome_iff_exists.mpr ⟨a,(eventOf_iff ..).mpr ⟨ha,realized⟩⟩,
            (ih (row.property.2 _ hm) hc).mpr ⟨pre,o,hpre,ho,rest⟩⟩

/-- At the minimum possible depth, every tail consumes exactly one event
and the head consumes exactly one packet. Run those checked rows directly. -/
def tightReachability {env : RecEnv s} {p : Program true env} (compiled : p.Compiled)
    (rootChecks : RestrictionChecks s) {bodyChecks live}
    (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : (compiled.initial rootChecks).checked.Valid live)
    (rs : List (ReconfigSet s)) (ing out : Predicate s)
    (i : { i : s.Packet // ∀ j, ing.holds j → j = i }) :
    { verdict : Bool // verdict = true ↔
        EndpointReachable p (some (rs.length + 1)) rs (.test ing) (.test out) } :=
  ⟨ing.eval i.val && search support (compiled.initial rootChecks).checked valid i.val out rs,
    by rw [Bool.and_eq_true, search_correct support valid compiled.corr]; exact (tight_iff i.property).symm⟩

private def packetPolicy : MoveLabel s → Option (NetKAT s)
  | .visible (.packet n) => some n
  | _ => none

private theorem packetPolicy_correct (l : MoveLabel s) (i o : s.Packet) :
    (∃ n, packetPolicy l = some n ∧ Semantics n i o) ↔
      l.Realizes [i] [] (.packet i o) [] [o] := by
  constructor
  · rintro ⟨n, h, sem⟩
    cases l with
    | visible a =>
      cases a with
      | packet p =>
        change some p = some n at h
        cases h
        exact .packet ((historySemantics_singleton_iff_packetSemantics ..).mpr sem)
      | rcfg => contradiction
    | recv | send => contradiction
  · intro h
    cases h with
    | packet h => exact ⟨_, rfl, (historySemantics_singleton_iff_packetSemantics ..).mp h⟩

private def policies {G : ProcessGraph s} {bodyChecks live}
    (support : ProjectionSupport G bodyChecks live) (state : CheckedResidual s)
    (valid : state.Valid live) : List (ReconfigSet s) → List (NetKAT s)
  | [] => (TraceSafety.checkedRow support state valid).val.filterMap (packetPolicy ∘ Prod.fst)
  | r :: rs =>
    let row := TraceSafety.checkedRow support state valid
    row.val.attach.flatMap fun m =>
      if (eventOf r m.val.1).isSome then
        policies support m.val.2 (row.property.2 _ m.property) rs
      else []

private theorem policies_correct {G : ProcessGraph s} {bodyChecks live}
    (support : ProjectionSupport G bodyChecks live) {env : RecEnv s} {p : DyNetKAT s}
    {state : CheckedResidual s} (valid : state.Valid live) (corr : Corr G env p state.proc)
    (i o : s.Packet) (rs : List (ReconfigSet s)) :
    (∃ n ∈ policies support state valid rs, Semantics n i o) ↔
      ∃ pre, OnePerStage rs pre ∧ SourceTrace env p (pre ++ [.packet i o]) := by
  induction rs generalizing p state with
  | nil =>
    let row := TraceSafety.checkedRow support state valid
    change (∃ n ∈ row.val.filterMap _, Semantics n i o) ↔ _
    simp only [OnePerStage, List.mem_filterMap, Function.comp_apply]
    constructor
    · rintro ⟨n, ⟨m, mem, hn⟩, sem⟩
      obtain ⟨q, step, _⟩ := (row.property.1.source_steps corr [i] [] (.packet i o) [] [o]).1
        m.1 m.2.proc (List.mem_map.mpr ⟨m,mem,rfl⟩) ((packetPolicy_correct ..).mp ⟨n,hn,sem⟩)
      exact ⟨[],rfl,sourceTrace_cons_actionStep.mpr ⟨q,step,sourceTrace_nil ..⟩⟩
    · rintro ⟨_,rfl,tr⟩
      obtain ⟨q, step, _⟩ := sourceTrace_cons_actionStep.mp tr
      obtain ⟨l, _, mem, realized, _⟩ :=
        (row.property.1.source_steps corr [i] [] (.packet i o) [] [o]).2 q step
      obtain ⟨m, hm, eq⟩ := List.mem_map.mp mem
      have same : m.1 = l := congrArg Prod.fst eq
      obtain ⟨n,hn,sem⟩ := (packetPolicy_correct ..).mpr (same.symm ▸ realized)
      exact ⟨n,⟨m,hm,hn⟩,sem⟩
  | cons r rs ih =>
    let row := TraceSafety.checkedRow support state valid
    unfold policies
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨n, ⟨⟨m, mem⟩, _, belongs⟩, sem⟩
      split at belongs
      · rename_i selected
        obtain ⟨a, he⟩ := Option.isSome_iff_exists.mp selected
        obtain ⟨ha, realized⟩ := (eventOf_iff ..).mp he
        obtain ⟨q, step, hc⟩ :=
          (row.property.1.source_steps corr (a.pendingFor []) [] a [] (a.handledAfter [])).1
            m.1 m.2.proc (List.mem_map.mpr ⟨m,mem,rfl⟩) realized
        obtain ⟨pre,hpre,tr⟩ := (ih (row.property.2 m mem) hc).mp ⟨n,belongs,sem⟩
        exact ⟨a::pre,⟨ha,hpre⟩,sourceTrace_cons_actionStep.mpr ⟨q,step,tr⟩⟩
      · contradiction
    · rintro ⟨pre,hpre,tr⟩
      cases pre with
      | nil => contradiction
      | cons a pre =>
        obtain ⟨ha,hpre⟩ := hpre
        obtain ⟨q,step,rest⟩ := sourceTrace_cons_actionStep.mp tr
        obtain ⟨l,target,mem,realized,hc⟩ :=
          (row.property.1.source_steps corr (a.pendingFor []) [] a [] (a.handledAfter [])).2 q step
        obtain ⟨m, hm, eq⟩ := List.mem_map.mp mem
        cases m with
        | mk label next =>
          cases eq
          obtain ⟨n,hn,sem⟩ := (ih (row.property.2 _ hm) hc).mpr ⟨pre,hpre,rest⟩
          have selected := Option.isSome_iff_exists.mpr ⟨a,(eventOf_iff ..).mpr ⟨ha,realized⟩⟩
          exact ⟨n, ⟨⟨(label,next),hm⟩,by simp,by simpa only [dif_pos selected, if_pos selected] using hn⟩,sem⟩

/-- Packet policies contributing to the head at the minimum selector depth. -/
def tightHead {env : RecEnv s} {p : Program true env} (compiled : p.Compiled)
    (rootChecks : RestrictionChecks s) {bodyChecks live}
    (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : (compiled.initial rootChecks).checked.Valid live)
    (rs : List (ReconfigSet s)) :
    { ns : List (NetKAT s) // ∀ i o,
      (∃ n ∈ ns, Semantics n i o) ↔
        ∃ word, QueryWord rs i o word ∧ p.Trace word ∧ word.length ≤ rs.length + 1 } := by
  refine ⟨policies support (compiled.initial rootChecks).checked valid rs, ?_⟩
  intro i o
  rw [policies_correct support valid compiled.corr]
  constructor
  · rintro ⟨pre,one,trace⟩
    obtain ⟨seg,len⟩ := one_segments one
    exact ⟨pre ++ [Action.packet i o], ⟨pre,[],seg,by simp,rfl⟩,trace,by simp [len]⟩
  · rintro ⟨_,⟨pre,head,seg,_,rfl⟩,trace,budget⟩
    have lower := segments_length seg
    simp at budget
    have empty : head = [] := List.length_eq_zero_iff.mp (by omega)
    subst head
    exact ⟨pre,segments_tight seg (by omega),by simpa using trace⟩

end DyNetKAT.DyNetKAT
