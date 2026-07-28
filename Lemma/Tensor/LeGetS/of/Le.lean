import Lemma.Tensor.BFnGetS.of.BFn
import Lemma.Tensor.GtLength
import Lemma.Tensor.Le.is.LeDataS
open Tensor


@[main, fin]
private lemma main
  [LE α]
  {A B : Tensor α s}
-- given
  (h : A ≤ B)
  (i : Fin A.length) :
-- imply
  A[i] ≤ (B[i]'(GtLength i B)) :=
-- proof
  BFnGetS.of.BFn (R := LE.le) (R₀ := LE.le) Le.is.LeDataS h i


-- created on 2026-07-27
-- updated on 2026-07-28
