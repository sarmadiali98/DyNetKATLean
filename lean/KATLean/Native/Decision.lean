import KATLean.Native.Symbolic
import KATLean.Native.Search

namespace KATLean.Native

variable {T A : Type} [BooleanAlphabet T] [Encodable T] [Encodable A] [Fintype A] [DecidableEq T] [DecidableEq A]

abbrev StatePair (T A : Type) := State T A × State T A

def pairRegions (pair : StatePair T A) (a : A) : Regions T (StatePair T A) :=
  combine Prod.mk (transitionRegions pair.1 a) (transitionRegions pair.2 a)

omit [Fintype A] in
theorem pairRegions_correct (pair : StatePair T A) (a : A) :
    Covers (pairRegions pair a) (fun v => (transition pair.1 v a, transition pair.2 v a)) :=
  covers_combine _ (transitionRegions_correct _ _) (transitionRegions_correct _ _)

def successors (pair : StatePair T A) : Finset (StatePair T A) :=
  Finset.univ.biUnion (fun a : A => ((pairRegions pair a).map Prod.snd).toFinset)

theorem mem_successors_iff (pair target : StatePair T A) : target ∈ successors pair ↔
    ∃ atom action, target = (transition pair.1 atom action, transition pair.2 atom action) := by
  constructor
  · intro member
    obtain ⟨a, _, region⟩ := Finset.mem_biUnion.mp member
    obtain ⟨⟨g, state⟩, member, same⟩ := List.mem_map.mp (List.mem_toFinset.mp region)
    have sat : Boolean.sat g.1 = true := by
      obtain ⟨l, x, r, y, _, _, sat, eq, _⟩ := (mem_combine _ _ _ _ _).mp member
      simpa [eq] using sat
    obtain ⟨v, accepted⟩ := (Boolean.sat_correct _).mp sat
    have accepted' : Boolean.eval g.1 (encodeAtom (decodeAtom v)) = true := by simpa using accepted
    exact ⟨decodeAtom v, a, same ▸ (pairRegions_correct pair a).1 g state member _ accepted'⟩
  · rintro ⟨atom, action, rfl⟩
    obtain ⟨g, member, _⟩ := (pairRegions_correct pair action).2 atom
    exact Finset.mem_biUnion.mpr ⟨action, Finset.mem_univ _, List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨(g, _), member, rfl⟩)⟩

def expand (visited : Finset (StatePair T A)) : Finset (StatePair T A) :=
  visited ∪ visited.biUnion successors

def initial (p q : Expr T A) : StatePair T A := ({p}, {q})

/-- A cardinality bound on all determinized state pairs. Only this natural
number is evaluated; the powerset carrier in the proof is not constructed. -/
def pairBound (p q : Expr T A) : Nat := 2 ^ ((support p).card + (support q).card)

def explored (p q : Expr T A) : Finset (StatePair T A) :=
  saturate expand (pairBound p q) {initial p q}

/-- Canonical symbolic output comparison, without truth-assignment enumeration. -/
def sameOutput (pair : StatePair T A) : Bool :=
  decide (outputGuard pair.1 = outputGuard pair.2)

omit [Fintype A] [DecidableEq T] [DecidableEq A] in
theorem sameOutput_correct (pair : StatePair T A) : sameOutput pair = true ↔
    ∀ atom, output pair.1 atom = output pair.2 atom := by
  rw [sameOutput, decide_eq_true_eq]
  constructor
  · intro h atom
    rw [← outputGuard_correct, ← outputGuard_correct, h]
  · intro h
    apply Boolean.guard_ext _ _ |>.mpr
    intro v
    have eq := h (decodeAtom v)
    rw [← outputGuard_correct, ← outputGuard_correct] at eq
    simpa using eq

/-- Complete guarded-language decision. Universal abstract KAT algebraic
completeness is a separate theorem and is not assumed here. -/
def decideLanguageEquiv (p q : Expr T A) : Bool := decide (∀ pair ∈ explored p q, sameOutput pair = true)

private theorem grows (visited : Finset (StatePair T A)) : visited ⊆ expand visited :=
  Finset.subset_union_left

private theorem mem_successors (pair : StatePair T A) (atom : Atom T) (action : A) :
    (transition pair.1 atom action, transition pair.2 atom action) ∈ successors pair :=
  (mem_successors_iff _ _).mpr ⟨atom, action, rfl⟩

private theorem carrier_supported (p q : Expr T A) :
    let carrier := (support p).powerset ×ˢ (support q).powerset
    ({initial p q} : Finset (StatePair T A)) ⊆ carrier ∧
      ∀ visited, visited ⊆ carrier → expand visited ⊆ carrier := by
  let carrier := (support p).powerset ×ˢ (support q).powerset
  have supported : ({initial p q} : Finset (StatePair T A)) ⊆ carrier := by
    intro pair member
    obtain rfl := Finset.mem_singleton.mp member
    simp [carrier, initial, support]
  have preserves (visited : Finset (StatePair T A)) (h : visited ⊆ carrier) :
      expand visited ⊆ carrier := by
    apply Finset.union_subset h
    intro pair member
    obtain ⟨source, hs, hm⟩ := Finset.mem_biUnion.mp member
    obtain ⟨atom, action, rfl⟩ := (mem_successors_iff source pair).mp hm
    have sourceSupported := Finset.mem_product.mp (h hs)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (transition_supported p (Finset.mem_powerset.mp sourceSupported.1) atom action),
       Finset.mem_powerset.mpr (transition_supported q (Finset.mem_powerset.mp sourceSupported.2) atom action)⟩
  exact ⟨supported, preserves⟩

theorem explored_supported (p q : Expr T A) {pair : StatePair T A} (h : pair ∈ explored p q) :
    pair.1 ⊆ support p ∧ pair.2 ⊆ support q := by
  obtain ⟨hstart, hstep⟩ := carrier_supported p q
  have hm := saturate_invariant expand _ hstep _ _ hstart h
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hm
  exact ⟨Finset.mem_powerset.mp hp, Finset.mem_powerset.mp hq⟩

theorem explored_closed (p q : Expr T A) : expand (explored p q) = explored p q := by
  obtain ⟨hstart, hstep⟩ := carrier_supported p q
  apply saturate_closed expand _ grows hstep _ _ hstart
  simp [pairBound, Finset.card_product, Finset.card_powerset, pow_add]

theorem successor_explored {p q : Expr T A} {pair : StatePair T A}
    (member : pair ∈ explored p q) (atom : Atom T) (action : A) :
    (transition pair.1 atom action, transition pair.2 atom action) ∈ explored p q := by
  rw [← explored_closed p q]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨pair, member, mem_successors pair atom action⟩)

private def PairEquivalent (pair : StatePair T A) : Prop :=
  ∀ atom word, StateAccept pair.1 atom word ↔ StateAccept pair.2 atom word

omit [BooleanAlphabet T] [Encodable T] [Encodable A] [Fintype A] in
private theorem equivalent_successor {pair : StatePair T A} (h : PairEquivalent pair)
    (atom : Atom T) (action : A) :
    PairEquivalent (transition pair.1 atom action, transition pair.2 atom action) := by
  intro next word
  exact (transition_correct pair.1 atom next action word).trans
    ((h atom ((action, next) :: word)).trans (transition_correct pair.2 atom next action word).symm)

theorem decideLanguageEquiv_sound (p q : Expr T A) (checked : decideLanguageEquiv p q = true) :
    LanguageEquivalent p q := by
  have outputs := of_decide_eq_true checked
  have language : ∀ word pair, pair ∈ explored p q → ∀ atom,
      StateAccept pair.1 atom word ↔ StateAccept pair.2 atom word := by
    intro word
    induction word with
    | nil =>
      intro pair member atom
      have equal := (sameOutput_correct pair).mp (outputs pair member) atom
      rw [← output_correct, ← output_correct, equal]
    | cons first rest ih =>
      intro pair member atom
      rw [← transition_correct pair.1 atom first.2 first.1 rest,
        ← transition_correct pair.2 atom first.2 first.1 rest]
      exact ih _ (successor_explored member atom first.1) first.2
  intro atom word
  have start : initial p q ∈ explored p q :=
    subset_saturate expand grows _ _ (Finset.mem_singleton_self _)
  simpa [initial, StateAccept] using language word (initial p q) start atom

theorem decideLanguageEquiv_complete (p q : Expr T A) (equivalent : LanguageEquivalent p q) :
    decideLanguageEquiv p q = true := by
  have invariant : ∀ pair ∈ explored p q, PairEquivalent pair := by
    apply saturate_invariant expand (fun visited => ∀ pair ∈ visited, PairEquivalent pair) ?_ _ _ ?_
    · intro visited inv pair member
      rcases Finset.mem_union.mp member with old | added
      · exact inv pair old
      · obtain ⟨source, hs, hm⟩ := Finset.mem_biUnion.mp added
        obtain ⟨atom, action, rfl⟩ := (mem_successors_iff source pair).mp hm
        exact equivalent_successor (inv source hs) atom action
    · intro pair member
      obtain rfl := Finset.mem_singleton.mp member
      simpa [PairEquivalent, initial, StateAccept] using equivalent
  apply decide_eq_true
  intro pair member
  apply (sameOutput_correct pair).mpr
  intro atom
  apply Bool.eq_iff_iff.mpr
  rw [output_correct, output_correct]
  exact invariant pair member atom []

theorem decideLanguageEquiv_correct (p q : Expr T A) :
    decideLanguageEquiv p q = true ↔ LanguageEquivalent p q :=
  ⟨decideLanguageEquiv_sound p q, decideLanguageEquiv_complete p q⟩

end KATLean.Native
