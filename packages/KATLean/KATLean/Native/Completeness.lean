import KATLean.Native.TermModel
import KATLean.Native.SymbolicSimulation

namespace KATLean.Native

variable {T A : Type}
variable [BooleanAlphabet T] [Encodable T] [Encodable A] [Fintype A]
variable [DecidableEq T] [DecidableEq A]

/-- Guarded-string language equality is valid in every abstract KATLean model.
The symbolic pair system transports the two least derivative solutions. -/
theorem LanguageEquivalent.algebraic {p q : Expr T A} (h : LanguageEquivalent p q) :
    AlgebraicallyEquivalent p q := by
  intro K B _ _ kat actions tests
  exact decideLanguageEquiv_algebraic p q (decideLanguageEquiv_complete p q h) kat actions tests

/-- Guarded-string completeness for the inductive pure KAT proof system. -/
theorem language_to_equational {p q : Expr T A} (h : LanguageEquivalent p q) :
    Equational p q :=
  h.algebraic.equational

theorem relational_to_equational {p q : Expr T A} (h : RelationalEquivalent p q) :
    Equational p q :=
  language_to_equational ((relational_iff_language p q).mp h)

theorem relationalEquivalent_iff_equational (p q : Expr T A) :
    RelationalEquivalent p q ↔ Equational p q :=
  ⟨relational_to_equational, fun h => h.algebraic_sound.relational⟩

/-- The symbolic native decision procedure decides derivability in pure KAT. -/
theorem decideEquiv_iff_equational (p q : Expr T A) :
    decideEquiv p q = true ↔ Equational p q :=
  (decideEquiv_correct p q).trans (relationalEquivalent_iff_equational p q)

theorem decideEquiv_iff_algebraicallyEquivalent (p q : Expr T A) :
    decideEquiv p q = true ↔ AlgebraicallyEquivalent p q :=
  (decideEquiv_iff_equational p q).trans (algebraicallyEquivalent_iff_equational p q).symm

theorem decideEquiv_false_not_equational {p q : Expr T A} (h : decideEquiv p q = false) :
    ¬ Equational p q := by
  intro eq
  rw [eq.solver_positive] at h
  contradiction

theorem decideEquiv_false_not_algebraicallyEquivalent {p q : Expr T A}
    (h : decideEquiv p q = false) : ¬ AlgebraicallyEquivalent p q :=
  fun valid => decideEquiv_false_not_equational h valid.equational

end KATLean.Native
