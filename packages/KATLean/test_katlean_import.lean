import KATLean
import KATLean.Native

open scoped Computability

example {K : Type*} [KleeneAlgebra K] (a : K) : 1 + a * a∗ = a∗ :=
  KATLean.star_unfold_left a

example : KATLean.Rel Nat := KATLean.Rel.test {n | n = 0}
