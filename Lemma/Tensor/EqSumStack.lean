import sympy.Basic
import sympy.tensor.stack


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α s) :
-- imply
  ∑ i < 1, X = X := by
-- proof
  sorry


-- created on 2026-07-22
