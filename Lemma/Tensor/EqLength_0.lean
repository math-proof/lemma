import torch.Tensor
import sympy.Basic


@[main]
private lemma main
-- given
  (X : Tensor α []) :
-- imply
  X.length = 0 := by
-- proof
  simp [Tensor.length]


-- created on 2025-06-24
