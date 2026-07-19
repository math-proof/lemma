import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqMul0_0
open Tensor


@[main]
private lemma main
  [MulZeroClass α] [NoZeroDivisors α]
  {X : Tensor α s}
-- given
  (h : X = 0)
  (a : α) :
-- imply
  X * a = 0 :=
-- proof
  h.symm.subst (motive := fun X : Tensor α s => X * a = 0) (EqMul0_0 s a)


-- created on 2025-12-08
