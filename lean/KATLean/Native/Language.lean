import KATLean.Native.Syntax

namespace KATLean.Native

abbrev Atom (T : Type) := T → Bool
abbrev Word (T A : Type) := List (A × Atom T)

/-- A guarded word consists of its initial atom and these action/next-atom
pairs. The last atom is fused when concatenating words. -/
def finish {T A : Type} (initial : Atom T) : Word T A → Atom T
  | [] => initial
  | (_, next) :: rest => finish next rest

@[simp] theorem finish_nil {T A : Type} (initial : Atom T) :
    finish (A := A) initial [] = initial := rfl

@[simp] theorem finish_cons {T A : Type} (initial next : Atom T) (a : A) (rest : Word T A) :
    finish initial ((a, next) :: rest) = finish next rest := rfl

@[simp] theorem finish_append {T A : Type} (initial : Atom T) (u v : Word T A) :
    finish initial (u ++ v) = finish (finish initial u) v := by
  induction u generalizing initial with
  | nil => rfl
  | cons first rest ih => exact ih first.2

/-- Standard guarded-string semantics with fusion at the shared boundary atom.
Star admits every finite number of iterations, including empty iterations. -/
inductive Accept {T A : Type} : Expr T A → Atom T → Word T A → Prop
  | one (atom) : Accept .one atom []
  | test (atom predicate) : predicate.eval atom = true → Accept (.test predicate) atom []
  | action (atom next name) : Accept (.action name) atom [(name, next)]
  | plusLeft : Accept p atom word → Accept (.plus p q) atom word
  | plusRight : Accept q atom word → Accept (.plus p q) atom word
  | seq : Accept p atom u → Accept q (finish atom u) v → Accept (.seq p q) atom (u ++ v)
  | starNil (atom p) : Accept (.star p) atom []
  | starCons : Accept p atom u → Accept (.star p) (finish atom u) v →
      Accept (.star p) atom (u ++ v)

theorem accept_seq_iff {T A : Type} {p q : Expr T A} {atom : Atom T} {word : Word T A} :
    Accept (.seq p q) atom word ↔
      ∃ u v, word = u ++ v ∧ Accept p atom u ∧ Accept q (finish atom u) v := by
  constructor
  · intro h
    cases h with
    | seq hp hq => exact ⟨_, _, rfl, hp, hq⟩
  · rintro ⟨u, v, rfl, hp, hq⟩
    exact .seq hp hq

/-- Equivalence in the guarded-string model. Connection to universal KAT
algebraic validity requires a separate completeness theorem. -/
def LanguageEquivalent {T A : Type} (p q : Expr T A) : Prop :=
  ∀ atom word, Accept p atom word ↔ Accept q atom word

theorem nullable_correct {T A : Type} (e : Expr T A) (atom : Atom T) :
    (nullable e).eval atom = true ↔ Accept e atom [] := by
  induction e with
  | zero | action => constructor <;> intro h <;> cases h
  | one => exact ⟨fun _ => .one atom, fun _ => rfl⟩
  | test predicate => exact ⟨.test atom predicate, fun h => by cases h; assumption⟩
  | plus p q ihp ihq =>
    simp only [nullable, Test.eval, Bool.or_eq_true, ihp, ihq]
    exact ⟨fun h => h.elim Accept.plusLeft Accept.plusRight, fun h => by
      cases h with
      | plusLeft hp => exact Or.inl hp
      | plusRight hq => exact Or.inr hq⟩
  | seq p q ihp ihq =>
    simp only [nullable, Test.eval, Bool.and_eq_true, ihp, ihq]
    constructor
    · rintro ⟨hp, hq⟩
      exact .seq hp hq
    · intro h
      obtain ⟨u, v, eq, hp, hq⟩ := accept_seq_iff.mp h
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp eq.symm
      exact ⟨hp, hq⟩
  | star p ih => exact ⟨fun _ => .starNil atom p, fun _ => rfl⟩

/-- A nonempty star trace has a first nonempty iteration. This handles
nullable bodies without discarding zero-action iterations by assumption. -/
theorem Accept.star_nonempty {T A : Type} {e : Expr T A} {atom : Atom T} {word : Word T A}
    (accepted : Accept e atom word) : ∀ p, e = .star p → word ≠ [] →
      ∃ u v, u ≠ [] ∧ word = u ++ v ∧ Accept p atom u ∧ Accept (.star p) (finish atom u) v := by
  induction accepted with
  | one | test | action | plusLeft | plusRight | seq => intros p impossible; cases impossible
  | starNil => intros p _ nonempty; exact (nonempty rfl).elim
  | @starCons p atom u v hp hrest ihp ihrest =>
    intro body eq nonempty
    cases eq
    cases u with
    | nil => exact ihrest p rfl nonempty
    | cons first tail => exact ⟨first :: tail, v, by simp, rfl, hp, hrest⟩

end KATLean.Native
