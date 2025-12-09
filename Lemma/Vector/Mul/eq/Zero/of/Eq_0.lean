import Lemma.Vector.EqMul0_0
import sympy.vector.vector
open Vector


@[main]
private lemma main
  [MulZeroClass α] [NoZeroDivisors α]
  {x : List.Vector α n}
-- given
  (h : x = 0)
  (a : α) :
-- imply
  x * a = 0 := by
-- proof
  subst h
  apply EqMul0_0


-- created on 2025-12-08
