import torch.Tensor.Basic
import sympy.Basic


@[main]
private lemma main
  [Add α]
-- given
  (A B : Tensor α s) :
-- imply
  (A + B).data = A.data + B.data :=
-- proof
  rfl


-- created on 2025-06-22
