import sympy.Basic
import torch.Tensor.Basic


@[main, grind =]
private lemma main
-- given
  (X : Tensor α (n :: s)) :
-- imply
  X.length = n := by
-- proof
  simp [Tensor.length]


-- created on 2025-12-08
