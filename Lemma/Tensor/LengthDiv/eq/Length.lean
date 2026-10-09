import torch.Tensor
import sympy.Basic


@[path]
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


@[path]
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
