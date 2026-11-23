import DyNetKATLean

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.NormalizationAdmissibilityTests

open DyNetKAT.NetKAT

private abbrev node := auxNode 0
private abbrev loopRef : GProc := .ref node
private abbrev tick : GProc := .rcfgPrefix "tick" .id loopRef
private abbrev loopBody : GProc := .choice loopRef tick

private def selfGraph (body : GProc) (h : gprocRefs body ⊆ {node}) : ProcessGraph :=
  ⟨{node}, loopRef, fun _ => body, by simp [gprocRefs], fun _ _ => h⟩

private def silentCycle : ProcessGraph := selfGraph loopRef (by simp [gprocRefs])
private def productiveCycle : ProcessGraph := selfGraph loopBody (by simp [gprocRefs])

private def silentCandidate : NormalizationCandidate 0 :=
  ⟨[node], fun _ => loopRef, fun _ => []⟩

private def productiveCandidate : NormalizationCandidate 0 :=
  ⟨[node], fun _ => loopRef, fun _ => [(.rcfg "tick" .id, 0)]⟩

private theorem silentExact : NormalizationExact silentCycle silentCandidate := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i pt hl a q pt' hl'
    have hNo := no_gstep_ref_two_cycle silentCycle node node rfl rfl pt hl a ⟨q, pt', hl'⟩
    simp only [silentCandidate, List.not_mem_nil, false_and, exists_false, iff_false]
    exact fun h => hNo h.2
  · intro i j l hm
    exact (List.not_mem_nil hm).elim
  · exact fun i => Or.inl (Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)))

private def LoopSource (p : GProc) : Prop :=
  p = loopRef ∨ p = loopBody ∨ p = tick

private theorem tickOnly {src dst : GConfig} {a : Action}
    (hs : GStep productiveCycle src a dst) (hSrc : LoopSource src.proc) :
    a = .rcfg "tick" .id ∧ dst.proc = loopRef ∧
      dst.pending = src.pending ∧ dst.handled = src.handled := by
  induction hs with
  | var _ _ _ _ _ _ _ _ ih => exact ih (Or.inr (Or.inl rfl))
  | choice_l _ _ _ _ _ _ _ _ _ ih =>
      rcases hSrc with h | h | h
      · cases h
      · cases h
        exact ih (Or.inl rfl)
      · cases h
  | choice_r _ _ _ _ _ _ _ _ _ ih =>
      rcases hSrc with h | h | h
      · cases h
      · cases h
        exact ih (Or.inr (Or.inr rfl))
      · cases h
  | rcfg =>
      rcases hSrc with h | h | h <;> cases h
      exact ⟨rfl, rfl, rfl, rfl⟩
  | seq_ok | par_l | par_r | left_merge | comm_merge_recv_send | comm_merge_send_recv |
    recv | send | sync_recv_send | sync_send_recv | project | restrict =>
      rcases hSrc with h | h | h <;> cases h

private theorem productiveExact : NormalizationExact productiveCycle productiveCandidate := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i pt hl a q pt' hl'
    constructor
    · rintro ⟨_, h⟩
      obtain ⟨rfl, rfl, rfl, rfl⟩ := tickOnly h (Or.inl rfl)
      exact ⟨_, 0, by simp [productiveCandidate], rfl, .rcfg⟩
    · rintro ⟨l, j, hm, rfl, hr⟩
      change (l, j) ∈ [(.rcfg "tick" .id, 0)] at hm
      cases List.mem_singleton.mp hm
      cases hr
      exact ⟨trivial, .var _ _ _ _ _ _ _
        (.choice_r _ _ _ _ _ _ _ _ (.rcfg _ _ _ _ _))⟩
  · intro i j l hm
    change (l, j) ∈ [(.rcfg "tick" .id, 0)] at hm
    cases List.mem_singleton.mp hm
    rfl
  · exact fun i => Or.inl (Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)))

theorem finite_silent_cycle : HasFiniteDerivatives silentCycle :=
  (exists_exactNormalization_iff _).mp ⟨0, silentCandidate, silentExact⟩

theorem finite_productive_cycle : HasFiniteDerivatives productiveCycle :=
  (exists_exactNormalization_iff _).mp ⟨0, productiveCandidate, productiveExact⟩

-- A nonempty order must compute a first row. Every body needs the missing
-- self row. An empty order leaves the root reference unresolved.
private theorem self_graph_no_checked_certificate {body : GProc} {hBody : gprocRefs body ⊆ {node}}
    (hLocal : localMoves (referenceMoves []) body = none) :
    ¬ ∃ (n : Nat) (C : NormalizationCandidate n),
      checkNormalization (selfGraph body hBody) C = true := by
  intro h
  obtain ⟨_, _, order, refs, hRefs, hRows⟩ := (exists_checkedNormalization_iff _).mp h
  cases order with
  | nil =>
      have he : [] = refs := Option.some.inj hRefs
      subst refs
      obtain ⟨_, hRow⟩ := hRows (selfGraph body hBody).root .refl
      cases hRow
  | cons i rest =>
      simp [buildReferenceRows, selfGraph, hLocal] at hRefs

theorem silent_cycle_no_checked_certificate :
    ¬ ∃ (n : Nat) (C : NormalizationCandidate n), checkNormalization silentCycle C = true :=
  self_graph_no_checked_certificate rfl

theorem productive_cycle_no_checked_certificate :
    ¬ ∃ (n : Nat) (C : NormalizationCandidate n), checkNormalization productiveCycle C = true :=
  self_graph_no_checked_certificate rfl

#guard !(checkNormalization silentCycle silentCandidate)
#guard !(checkNormalization productiveCycle productiveCandidate)
#guard (normalizeCertifiedGraph silentCandidate silentExact).nodes.card == 1
#guard (normalizeCertifiedGraph productiveCandidate productiveExact).nodes.card == 1
#guard (Internal.safetyCheckCertifiedGraph productiveCandidate productiveExact {("tick", .id)} .id .id) ==
  ⟨.isZero true, .nonzero false⟩

private def nested (L M : Set CommunicationAction) : GProc :=
  .restrict L (.restrict M (.rcfgPrefix "go" .id .deadlock))

private def nestedAfter (L M : Set CommunicationAction) : GProc :=
  .restrict L (.restrict M .deadlock)

private def nestedGraph (L M : Set CommunicationAction) : ProcessGraph :=
  ⟨∅, nested L M, fun _ => .deadlock, by simp [nested, gprocRefs], by simp⟩

private def nestedCandidate (L M : Set CommunicationAction) : NormalizationCandidate 1 :=
  ⟨[], fun i => if i = 0 then nested L M else nestedAfter L M,
    fun i => if i = 0 then [(.rcfg "go" .id, 1)] else []⟩

private theorem nestedExact (L M : Set CommunicationAction) :
    NormalizationExact (nestedGraph L M) (nestedCandidate L M) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i pt hl a q pt' hl'
    by_cases hi : i = 0
    · subst i
      constructor
      · rintro ⟨_, h⟩
        change GStep (nestedGraph L M) ⟨nested L M, pt, hl⟩ a ⟨q, pt', hl'⟩ at h
        cases h with
        | restrict _ _ _ _ _ _ _ _ _ hs =>
          cases hs with
          | restrict _ _ _ _ _ _ _ _ _ hs =>
            cases hs
            exact ⟨_, 1, by simp [nestedCandidate], rfl, .rcfg⟩
      · rintro ⟨l, j, hm, rfl, hr⟩
        change (l, j) ∈ [(.rcfg "go" .id, 1)] at hm
        cases List.mem_singleton.mp hm
        cases hr
        exact ⟨trivial, .restrict _ _ _ _ _ _ _ _ trivial
          (.restrict _ _ _ _ _ _ _ _ trivial (.rcfg _ _ _ _ _))⟩
    · simp only [nestedCandidate, if_neg hi, List.not_mem_nil, false_and,
        exists_false, iff_false, not_and]
      intro _ h
      change GStep (nestedGraph L M) ⟨nestedAfter L M, pt, hl⟩ a ⟨q, pt', hl'⟩ at h
      cases h with
      | restrict _ _ _ _ _ _ _ _ _ hs =>
        cases hs with
        | restrict _ _ _ _ _ _ _ _ _ hs => cases hs
  · intro i j l hm
    by_cases hi : i = 0
    · subst i
      change (l, j) ∈ [(.rcfg "go" .id, 1)] at hm
      cases List.mem_singleton.mp hm
      rfl
    · simp [nestedCandidate, hi] at hm
  · intro i
    by_cases hi : i = 0
    · exact Or.inl hi
    · rw [Fin.eq_one_of_ne_zero i hi]
      exact Or.inr ⟨0, .rcfg "go" .id, by decide, by simp [nestedCandidate]⟩

theorem finite_nested_restrictions (L M : Set CommunicationAction) :
    HasFiniteDerivatives (nestedGraph L M) :=
  (exists_exactNormalization_iff _).mp ⟨1, nestedCandidate L M, nestedExact L M⟩

theorem nested_no_checked_certificate (L M : Set CommunicationAction) :
    ¬ ∃ (n : Nat) (C : NormalizationCandidate n), checkNormalization (nestedGraph L M) C = true := by
  intro h
  have hAd := ((exists_checkedNormalization_iff _).mp h).2
  have hr := hAd.1 (nestedGraph L M).root .refl
  cases hr

#guard !(checkNormalization (nestedGraph ∅ Set.univ) (nestedCandidate ∅ Set.univ))
#guard (normalizeCertifiedGraph (nestedCandidate ∅ Set.univ) (nestedExact ∅ Set.univ)).nodes.card == 2

-- Availability and comparability are separate checks. Projection zero
-- skips the nested restriction when computing moves, while comparison
-- still sees the restriction in the derivative syntax.
example (L : Set CommunicationAction) :
    localMoves (fun _ => none) (.project 0 (.restrict L .deadlock)) = some [] ∧
    sameProcess (.project 0 (.restrict L .deadlock)) (.project 0 (.restrict L .deadlock)) = false :=
  ⟨rfl, rfl⟩

-- A restriction inside a parallel operand can suppress a handshake.
-- The restriction set is an arbitrary predicate in this statement.
theorem nested_sync_iff (G : ProcessGraph) (L : Set CommunicationAction) :
    GStep G ⟨.parallel (.restrict L (.send "sync" .id .deadlock))
      (.recv "sync" .id .deadlock), [], []⟩ (.rcfg "sync" .id)
      ⟨.parallel (.restrict L .deadlock) .deadlock, [], []⟩ ↔
    CommunicationAction.send "sync" .id ∉ L := by
  constructor
  · intro h
    cases h with
    | sync_recv_send _ _ _ _ _ _ _ _ hRecv _ =>
        cases hRecv with
        | restrict _ _ _ _ _ _ _ _ _ h => cases h
    | sync_send_recv _ _ _ _ _ _ _ _ hSend _ =>
        cases hSend with
        | restrict _ _ _ _ _ _ _ _ hAllowed _ => exact hAllowed
  · intro h
    exact .sync_send_recv _ _ _ _ _ _ _ _
      (.restrict L _ _ _ _ _ _ _ h (.send _ _ _ _ _)) (.recv _ _ _ _ _)

#print axioms sameProcess_self_iff
#print axioms localMoves_exists_iff
#print axioms normalizationAdmissible_iff
#print axioms exists_checkedNormalization_iff
#print axioms exists_exactNormalization_iff
#print axioms normalizeCertifiedGraph_correct
#print axioms safetyCheckCertifiedGraph_correct
#print axioms finite_silent_cycle
#print axioms finite_productive_cycle
#print axioms silent_cycle_no_checked_certificate
#print axioms productive_cycle_no_checked_certificate
#print axioms finite_nested_restrictions
#print axioms nested_no_checked_certificate
#print axioms nested_sync_iff

end DyNetKAT.DyNetKAT.NormalizationAdmissibilityTests
