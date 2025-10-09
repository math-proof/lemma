import sympy.tensor.functions
import Lemma.Tensor.Softmax.eq.Div_SumExp
import Lemma.Tensor.Sum.eq.GetEllipsisKeepdimSum.of.Get.gt.Zero
open Tensor


@[main]
private lemma main
  [Exp α]
  {dim : Fin s.length}
-- given
  (h : s[dim] > 0)
  (X : Tensor α s):
-- imply
  (X.softmax dim).sum dim = 1 := by
-- proof
  rw [Softmax.eq.Div_SumExp]
  rw [Sum.eq.GetEllipsisKeepdimSum.of.Get.gt.Zero h]
  sorry


-- created on 2025-10-03
-- updated on 2025-10-07
