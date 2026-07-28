import Lemma.Tensor.BFnGetS.of.BFn
import Lemma.Tensor.GtLength
import Lemma.Tensor.Lt.is.LtDataS
open Tensor


@[main, fin]
private lemma main
  [LT α]
  {A B : Tensor α s}
-- given
  (h : A < B)
  (i : Fin A.length) :
-- imply
  A[i] < (B[i]'(GtLength i B)) :=
-- proof
  BFnGetS.of.BFn (R := LT.lt) (R₀ := LT.lt) Lt.is.LtDataS h i


-- created on 2026-07-27
-- updated on 2026-07-28
