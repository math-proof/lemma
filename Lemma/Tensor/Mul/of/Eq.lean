import sympy.Basic
import torch.Tensor.Basic


@[main]
private lemma main
  [Mul α]
  {A B : Tensor α s}
-- given
  (h : A = B)
  (x : α) :
-- imply
  A * x = B * x := by
-- proof
  rw [h]


-- created on 2025-12-01
-- updated on 2025-12-03
