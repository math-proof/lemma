import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqMul0_0
open Vector Tensor


@[main]
private lemma main
  [MulZeroClass α] [NoZeroDivisors α]
  {X : Tensor α s}
-- given
  (h : X = 0)
  (a : α) :
-- imply
  X * a = 0 := by
-- proof
  subst h
  apply Eq.of.EqDataS
  apply EqMul0_0


-- created on 2025-12-08
