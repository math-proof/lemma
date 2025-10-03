import sympy.tensor.functions
import Lemma.Tensor.Softmax.eq.Div_SumExp
open Tensor


@[main]
private lemma main
  [Exp α] [Zero α] [Div α] [One α]
-- given
  (x : Tensor α s)
  (dim : ℕ) :
-- imply
  (x.softmax dim).sum dim = 1 := by
-- proof
  rw [Softmax.eq.Div_SumExp]
  sorry


-- created on 2025-10-03
