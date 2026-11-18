import KATLean

namespace KATLean.Native

/-- Symbolic Boolean syntax. Primitive tests refer to an abstract alphabet. -/
inductive Test (T : Type) where
  | bot
  | top
  | atom (name : T)
  | conj (left right : Test T)
  | disj (left right : Test T)
  | neg (test : Test T)
  deriving DecidableEq, Repr

def Test.eval {T : Type} (valuation : T → Bool) : Test T → Bool
  | .bot => false
  | .top => true
  | .atom name => valuation name
  | .conj p q => p.eval valuation && q.eval valuation
  | .disj p q => p.eval valuation || q.eval valuation
  | .neg p => !(p.eval valuation)

def Test.interp {T B : Type} [BooleanAlgebra B] (valuation : T → B) : Test T → B
  | .bot => ⊥
  | .top => ⊤
  | .atom name => valuation name
  | .conj p q => p.interp valuation ⊓ q.interp valuation
  | .disj p q => p.interp valuation ⊔ q.interp valuation
  | .neg p => (p.interp valuation)ᶜ

/-- Finite solver syntax, independent of packet schemas and process syntax. -/
inductive Expr (T A : Type) where
  | zero
  | one
  | action (name : A)
  | test (predicate : Test T)
  | plus (left right : Expr T A)
  | seq (left right : Expr T A)
  | star (body : Expr T A)
  deriving DecidableEq, Repr

open scoped Computability

def Expr.interp {T A K B : Type} [KleeneAlgebra K] [BooleanAlgebra B]
    (kat : KAT K B) (actions : A → K) (tests : T → B) : Expr T A → K
  | .zero => 0
  | .one => 1
  | .action name => actions name
  | .test predicate => kat.embed (predicate.interp tests)
  | .plus p q => p.interp kat actions tests + q.interp kat actions tests
  | .seq p q => p.interp kat actions tests * q.interp kat actions tests
  | .star p => (p.interp kat actions tests)∗

/-- The empty guarded string's acceptance condition remains a Boolean formula. -/
def nullable {T A : Type} : Expr T A → Test T
  | .zero | .action _ => .bot
  | .one | .star _ => .top
  | .test predicate => predicate
  | .plus p q => .disj (nullable p) (nullable q)
  | .seq p q => .conj (nullable p) (nullable q)

end KATLean.Native
