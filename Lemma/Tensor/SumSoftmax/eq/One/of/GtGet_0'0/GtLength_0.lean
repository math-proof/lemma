import sympy.tensor.functions
import Lemma.Tensor.Softmax.eq.Div_SumExp
open Tensor


@[main]
private lemma main
  [ExpPos α]
-- given
  (h_s : s.length > 0)
  (h : s[0] > 0)
  (X : Tensor α s) :
-- imply
  (X.softmax 0).sum 0 = 1 := by
-- proof
  rw [Softmax.eq.Div_SumExp]
  unfold Tensor.sum_keepdim
  simp [h_s]
  sorry


-- created on 2025-10-07
