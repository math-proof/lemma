import sympy.Basic
import torch.functions


@[main]
private lemma main
  [Log α]
-- given
  (X : Tensor α s) :
-- imply
  (log X).data = log X.data :=
-- proof
  rfl


-- created on 2025-12-04
