import KATLean.Native.Model

namespace KATLean.Native

variable {T A : Type}

/-- The free trace model records an initial atom and the guarded prefix
already executed. It is a proof model, never an executable search state. -/
abbrev TraceState (T A : Type) := Atom T × Word T A

def traceTests (name : T) : Set (TraceState T A) :=
  {state | finish state.1 state.2 name = true}

def traceActions (name : A) : Rel (TraceState T A) :=
  ⟨fun source target => ∃ next, target = (source.1, source.2 ++ [(name, next)])⟩

@[simp] theorem observe_trace (state : TraceState T A) :
    observe traceTests state = finish state.1 state.2 := by
  funext name
  apply Bool.eq_iff_iff.mpr
  simp [observe, traceTests]

private theorem trace_shape {atom : Atom T} {word : Word T A} {source target : TraceState T A}
    (realized : Realizes traceActions traceTests atom word source target) :
    atom = finish source.1 source.2 ∧ target = (source.1, source.2 ++ word) := by
  induction word generalizing atom source with
  | nil =>
    exact ⟨by simpa using realized.start, by simpa using realized.2.symm⟩
  | cons first rest ih =>
    obtain ⟨observed, middle, ⟨next, rfl⟩, tail⟩ := realized
    obtain ⟨nextObserved, targetEq⟩ := ih tail
    have equal : first.2 = next := by simpa using nextObserved
    exact ⟨by simpa using observed, by simpa [← equal, List.append_assoc] using targetEq⟩

private theorem trace_realizes (source : TraceState T A) (word : Word T A) :
    Realizes traceActions traceTests (finish source.1 source.2) word source
      (source.1, source.2 ++ word) := by
  induction word generalizing source with
  | nil => exact ⟨(observe_trace source).symm, by simp⟩
  | cons first rest ih =>
    refine ⟨(observe_trace source).symm, (source.1, source.2 ++ [first]), ⟨first.2, rfl⟩, ?_⟩
    have tail := ih (source.1, source.2 ++ [first])
    simpa [List.append_assoc] using tail

/-- The guarded-string model is faithfully represented by a KATLean
relational interpretation. No language-model completeness is assumed. -/
theorem guarded_model_correct (e : Expr T A) (atom : Atom T) (word : Word T A) :
    (e.interp Rel.tests traceActions traceTests).holds (atom, []) (atom, word) ↔
      Accept e atom word := by
  rw [interp_iff_accept]
  constructor
  · rintro ⟨observed, consumed, accepted, realized⟩
    obtain ⟨sameAtom, sameWord⟩ := trace_shape realized
    have same : word = consumed := congrArg Prod.snd sameWord
    have observedEq : observed = atom := sameAtom
    simpa only [observedEq, same] using accepted
  · intro accepted
    exact ⟨atom, word, accepted, by simpa using trace_realizes (atom, []) word⟩

theorem relational_iff_language (p q : Expr T A) :
    RelationalEquivalent p q ↔ LanguageEquivalent p q := by
  constructor
  · intro equivalent atom word
    have model := equivalent (TraceState T A) traceActions traceTests
    rw [← guarded_model_correct, ← guarded_model_correct, model]
  · exact LanguageEquivalent.relational_sound

variable [BooleanAlphabet T] [Encodable T] [Encodable A] [Fintype A] [DecidableEq T] [DecidableEq A]

/-- Native equivalence over arbitrary relational KAT interpretations. -/
def decideEquiv (p q : Expr T A) : Bool := decideLanguageEquiv p q

theorem decideEquiv_correct (p q : Expr T A) :
    decideEquiv p q = true ↔ RelationalEquivalent p q :=
  (decideLanguageEquiv_correct p q).trans (relational_iff_language p q).symm

theorem decideEquiv_sound (p q : Expr T A) (checked : decideEquiv p q = true) :
    RelationalEquivalent p q := (decideEquiv_correct p q).mp checked

theorem decideEquiv_complete (p q : Expr T A) (equivalent : RelationalEquivalent p q) :
    decideEquiv p q = true := (decideEquiv_correct p q).mpr equivalent

/-- Failure entails a distinguishing guarded word. Concrete witness
extraction with predecessor storage remains a separate implementation step. -/
theorem inequivalent_witness (p q : Expr T A) (different : decideEquiv p q = false) :
    ∃ atom word, ¬ (Accept p atom word ↔ Accept q atom word) := by
  classical
  by_contra noWitness
  push_neg at noWitness
  have same := decideLanguageEquiv_complete p q noWitness
  change decideLanguageEquiv p q = false at different
  rw [different] at same
  cases same

end KATLean.Native
