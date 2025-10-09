import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  [Exp α]
-- given
  (x : Tensor α s)
  (dim : ℕ) :
-- imply
  x.softmax dim = exp x / ((exp x).sum dim).keepdim := by
-- proof
  unfold Tensor.softmax
  simp


-- created on 2025-10-03
