import sympy.tensor.Basic
import sympy.Basic


@[main, grind =]
private lemma main
-- given
  (X : Tensor α s)
  (f : α → β) :
-- imply
  (X.map f).length = X.length := by
-- proof
  unfold Tensor.length
  aesop


-- created on 2025-12-23
