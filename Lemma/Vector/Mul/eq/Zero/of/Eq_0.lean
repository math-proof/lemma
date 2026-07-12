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
  x * a = 0 :=
-- proof
  h.symm.subst (motive := fun x : List.Vector α n => x * a = 0) (EqMul0_0 n a)


-- created on 2025-12-08
