import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  [Exp α] [Zero α] [Div α]
-- given
  (x : Tensor α s) :
-- imply
  x.softmax = exp x / (exp x).sum := by
-- proof
  unfold Tensor.softmax
  simp


-- created on 2025-10-03
