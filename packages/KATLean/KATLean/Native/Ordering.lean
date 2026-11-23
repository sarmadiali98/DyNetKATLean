import KATLean.Native.Syntax
import Mathlib.Data.List.Lex
import Mathlib.Logic.Encodable.Basic

namespace KATLean.Native


private theorem split_code {a b c d : List Nat} (len : a.length = c.length)
    (eq : a ++ b = c ++ d) : a = c ∧ b = d := by
  have first := congrArg (List.take a.length) eq
  have second := congrArg (List.drop a.length) eq
  simpa [len] using And.intro first second

/-- Compact prefix codes: lengths delimit binary operands without converting
whole syntax trees into exponentially large pairing-code natural numbers. -/
def Test.orderCode [Encodable T] : Test T → List Nat
  | .bot => [0]
  | .top => [1]
  | .atom t => [2, Encodable.encode t]
  | .neg p => 3 :: p.orderCode
  | .conj p q => 4 :: p.orderCode.length :: (p.orderCode ++ q.orderCode)
  | .disj p q => 5 :: p.orderCode.length :: (p.orderCode ++ q.orderCode)

theorem Test.orderCode_injective [Encodable T] : Function.Injective (Test.orderCode (T := T)) := by
  intro p
  induction p with
  | bot => intro q eq; cases q <;> simp_all [Test.orderCode]
  | top => intro q eq; cases q <;> simp_all [Test.orderCode]
  | atom t =>
    intro q eq
    cases q <;> simp_all [Test.orderCode, Encodable.encode_inj]
  | neg p ih =>
    intro q eq
    cases q <;> simp [Test.orderCode] at eq ⊢
    exact ih eq
  | conj p q ihp ihq =>
    intro r eq
    cases r <;> simp only [Test.orderCode, List.cons.injEq, Nat.reduceEqDiff, false_and] at eq
    case conj left right =>
      obtain ⟨_, len, eq⟩ := eq
      obtain ⟨hp, hq⟩ := split_code len eq
      exact congrArg₂ Test.conj (ihp hp) (ihq hq)
  | disj p q ihp ihq =>
    intro r eq
    cases r <;> simp only [Test.orderCode, List.cons.injEq, Nat.reduceEqDiff, false_and] at eq
    case disj left right =>
      obtain ⟨_, len, eq⟩ := eq
      obtain ⟨hp, hq⟩ := split_code len eq
      exact congrArg₂ Test.disj (ihp hp) (ihq hq)

def Expr.orderCode [Encodable T] [Encodable A] : Expr T A → List Nat
  | .zero => [0]
  | .one => [1]
  | .action a => [2, Encodable.encode a]
  | .test p => 3 :: p.orderCode
  | .plus p q => 4 :: p.orderCode.length :: (p.orderCode ++ q.orderCode)
  | .seq p q => 5 :: p.orderCode.length :: (p.orderCode ++ q.orderCode)
  | .star p => 6 :: p.orderCode

theorem Expr.orderCode_injective [Encodable T] [Encodable A] :
    Function.Injective (Expr.orderCode (T := T) (A := A)) := by
  intro p
  induction p with
  | zero => intro q eq; cases q <;> simp_all [Expr.orderCode]
  | one => intro q eq; cases q <;> simp_all [Expr.orderCode]
  | action a => intro q eq; cases q <;> simp_all [Expr.orderCode, Encodable.encode_inj]
  | test p =>
    intro q eq
    cases q <;> simp_all [Expr.orderCode]
    exact Test.orderCode_injective eq
  | star p ih =>
    intro q eq
    cases q <;> simp [Expr.orderCode] at eq ⊢
    exact ih eq
  | plus p q ihp ihq =>
    intro r eq
    cases r <;> simp only [Expr.orderCode, List.cons.injEq, Nat.reduceEqDiff, false_and] at eq
    case plus left right =>
      obtain ⟨_, len, eq⟩ := eq
      obtain ⟨hp, hq⟩ := split_code len eq
      exact congrArg₂ Expr.plus (ihp hp) (ihq hq)
  | seq p q ihp ihq =>
    intro r eq
    cases r <;> simp only [Expr.orderCode, List.cons.injEq, Nat.reduceEqDiff, false_and] at eq
    case seq left right =>
      obtain ⟨_, len, eq⟩ := eq
      obtain ⟨hp, hq⟩ := split_code len eq
      exact congrArg₂ Expr.seq (ihp hp) (ihq hq)

end KATLean.Native
