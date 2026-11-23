import KATLean.Native.Derivatives
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset

namespace KATLean.Native

variable {T A : Type} [DecidableEq T] [DecidableEq A]

abbrev State (T A : Type) := Finset (Expr T A)

def StateAccept (state : State T A) (atom : Atom T) (word : Word T A) : Prop :=
  ∃ expression ∈ state, Accept expression atom word

def output (state : State T A) (atom : Atom T) : Bool :=
  decide (∃ e ∈ state, (nullable e).eval atom = true)

def transition (state : State T A) (atom : Atom T) (action : A) : State T A :=
  state.biUnion (fun e => derivative e atom action)

omit [DecidableEq T] [DecidableEq A] in
theorem output_correct (state : State T A) (atom : Atom T) :
    output state atom = true ↔ StateAccept state atom [] := by
  simp only [output, decide_eq_true_eq, StateAccept, nullable_correct]

theorem transition_correct (state : State T A) (atom next : Atom T) (action : A) (word : Word T A) :
    StateAccept (transition state atom action) next word ↔
      StateAccept state atom ((action, next) :: word) := by
  simp only [StateAccept, transition, Finset.mem_biUnion]
  constructor
  · rintro ⟨rest, ⟨e, member, step⟩, accepted⟩
    exact ⟨e, member, (derivative_correct e atom action next word).mpr ⟨rest, step, accepted⟩⟩
  · rintro ⟨e, member, accepted⟩
    obtain ⟨rest, step, accepted⟩ := (derivative_correct e atom action next word).mp accepted
    exact ⟨rest, ⟨e, member, step⟩, accepted⟩

theorem transition_supported (e : Expr T A) {state : State T A} (h : state ⊆ support e)
    (atom : Atom T) (action : A) : transition state atom action ⊆ support e := by
  intro rest member
  obtain ⟨source, hs, step⟩ := Finset.mem_biUnion.mp member
  exact support_closed e (h hs) atom action step

/-- Every determinized residual is a subset of one finite support. -/
theorem state_space_finite (e : Expr T A) : {state : State T A | state ⊆ support e}.Finite :=
  (support e).powerset.finite_toSet.subset (fun _ member => Finset.mem_powerset.mpr member)

end KATLean.Native
