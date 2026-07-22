import Lemma.Fin.Eq_0
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqGetUnsqueeze_0
open Fin Tensor


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  [_ < 1] X = X.unsqueeze 0 := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  have h_i := Eq_0 i
  subst h_i
  erw [EqGetUnsqueeze_0.fin]
  rw [EqGetStack.fn.fin]


-- created on 2026-07-22
