import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  [Exp α]
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  X.softmax d = exp X / ((exp X).sum d).keepdim := by
-- proof
  unfold Tensor.softmax
  simp


-- created on 2025-10-03
