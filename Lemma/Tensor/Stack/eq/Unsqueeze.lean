import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqGetUnsqueeze_0
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  [_ < 1] X = X.unsqueeze 0 := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  fin_cases i
  erw [EqGetUnsqueeze_0.fin]
  rw [EqGetStack.fin]


-- created on 2026-07-22
