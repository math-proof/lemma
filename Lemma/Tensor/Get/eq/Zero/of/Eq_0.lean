import Lemma.Tensor.EqGet0_0
import sympy.tensor.tensor
open Tensor


@[main, fin]
private lemma main
  [Zero α]
  {X : Tensor α s}
-- given
  (h : X = 0)
  (i : Fin X.length) :
-- imply
  X[i] = 0 := by
-- proof
  subst h
  apply EqGet0_0


-- created on 2025-12-06
