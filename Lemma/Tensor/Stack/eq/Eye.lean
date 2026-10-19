import sympy.matrices.expressions.special
import torch.eye


@[path]
private lemma main
  [AddMonoidWithOne α] [CharZero α] :
-- imply
  [i < n] [j < n] (KroneckerDelta i j) = Tensor.eye (α := α) n := by
-- proof
  unfold Tensor.eye
  rfl


-- created on 2018-04-16
