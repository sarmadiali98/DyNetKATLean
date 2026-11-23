import Mathlib.Data.Finset.Prod
import KATLean.Native.Automaton
import KATLean.Native.Search

namespace KATLean.Native.Explicit

variable {T A : Type} [Fintype T] [Fintype A] [DecidableEq T] [DecidableEq A]

abbrev StatePair (T A : Type) := State T A × State T A

def successors (pair : StatePair T A) : Finset (StatePair T A) :=
  Finset.univ.biUnion (fun atom : Atom T => Finset.univ.image (fun action : A =>
    (transition pair.1 atom action, transition pair.2 atom action)))

def expand (visited : Finset (StatePair T A)) : Finset (StatePair T A) :=
  visited ∪ visited.biUnion successors

def initial (p q : Expr T A) : StatePair T A := ({p}, {q})

/-- A cardinality bound on all determinized state pairs. Only this natural
number is evaluated; the powerset carrier in the proof is not constructed. -/
def pairBound (p q : Expr T A) : Nat := 2 ^ ((support p).card + (support q).card)

def explored (p q : Expr T A) : Finset (StatePair T A) :=
  saturate expand (pairBound p q) {initial p q}

/-- Exact comparison of propositional outputs over abstract test atoms.
This finite Boolean alphabet is independent of any concrete packet model. -/
def sameOutput (pair : StatePair T A) : Bool :=
  decide (∀ atom : Atom T, output pair.1 atom = output pair.2 atom)

/-- Complete guarded-language decision. Universal abstract KAT algebraic
completeness is a separate theorem and is not assumed here. -/
def decideLanguageEquiv (p q : Expr T A) : Bool := decide (∀ pair ∈ explored p q, sameOutput pair = true)

private theorem grows (visited : Finset (StatePair T A)) : visited ⊆ expand visited :=
  Finset.subset_union_left

private theorem mem_successors (pair : StatePair T A) (atom : Atom T) (action : A) :
    (transition pair.1 atom action, transition pair.2 atom action) ∈ successors pair :=
  Finset.mem_biUnion.mpr ⟨atom, Finset.mem_univ _, Finset.mem_image.mpr
    ⟨action, Finset.mem_univ _, rfl⟩⟩

private theorem explored_closed (p q : Expr T A) : expand (explored p q) = explored p q := by
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
    obtain ⟨atom, _, hm⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨action, _, rfl⟩ := Finset.mem_image.mp hm
    have sourceSupported := Finset.mem_product.mp (h hs)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (transition_supported p (Finset.mem_powerset.mp sourceSupported.1) atom action),
       Finset.mem_powerset.mpr (transition_supported q (Finset.mem_powerset.mp sourceSupported.2) atom action)⟩
  apply saturate_closed expand carrier grows preserves _ _ supported
  simp [carrier, pairBound, Finset.card_product, Finset.card_powerset, pow_add]

private theorem successor_explored {p q : Expr T A} {pair : StatePair T A}
    (member : pair ∈ explored p q) (atom : Atom T) (action : A) :
    (transition pair.1 atom action, transition pair.2 atom action) ∈ explored p q := by
  rw [← explored_closed p q]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨pair, member, mem_successors pair atom action⟩)

private def PairEquivalent (pair : StatePair T A) : Prop :=
  ∀ atom word, StateAccept pair.1 atom word ↔ StateAccept pair.2 atom word

omit [Fintype T] [Fintype A] in
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
      have equal := of_decide_eq_true (outputs pair member) atom
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
        obtain ⟨atom, _, hm⟩ := Finset.mem_biUnion.mp hm
        obtain ⟨action, _, rfl⟩ := Finset.mem_image.mp hm
        exact equivalent_successor (inv source hs) atom action
    · intro pair member
      obtain rfl := Finset.mem_singleton.mp member
      simpa [PairEquivalent, initial, StateAccept] using equivalent
  apply decide_eq_true
  intro pair member
  apply decide_eq_true
  intro atom
  apply Bool.eq_iff_iff.mpr
  rw [output_correct, output_correct]
  exact invariant pair member atom []

theorem decideLanguageEquiv_correct (p q : Expr T A) :
    decideLanguageEquiv p q = true ↔ LanguageEquivalent p q :=
  ⟨decideLanguageEquiv_sound p q, decideLanguageEquiv_complete p q⟩

end KATLean.Native.Explicit
