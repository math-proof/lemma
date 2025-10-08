import sympy.tensor.tensor
import sympy.Basic


@[main]
private lemma main
  [Div α]
-- given
  (A B : Tensor α s) :
-- imply
  (A / B).length = B.length := by
-- proof
  cases s <;>
  ·
    simp [Tensor.length]


@[main]
private lemma left
  [Div α]
-- given
  (A B : Tensor α s) :
-- imply
  (A / B).length = A.length := by
-- proof
  cases s <;>
  ·
    simp [Tensor.length]


-- created on 2025-10-08
