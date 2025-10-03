import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  [Exp α] [Zero α] [Div α]
-- given
  (x : Tensor α s)
  (dim : ℕ := s.length - 1):
-- imply
  x.softmax dim = exp x / (exp x).sum dim:= by
-- proof
  unfold Tensor.softmax
  simp


-- created on 2025-10-03
