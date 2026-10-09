import torch.Tensor.Basic
import sympy.Basic


@[path]
private lemma main
  [Neg α]
-- given
  (X : Tensor α s) :
-- imply
  (-X).data = -X.data :=
-- proof
  rfl


-- created on 2025-10-04
