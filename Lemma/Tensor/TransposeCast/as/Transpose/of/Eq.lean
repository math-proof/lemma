import stdlib.SEq
import sympy.Basic
import torch.Tensor.Basic
import torch.Tensor.permute


@[main, cast]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s)
  (i j : ℕ) :
-- imply
  (cast (congrArg (Tensor α) h) X).transpose i j ≃ X.transpose i j := by
-- proof
  subst h
  rfl


-- created on 2026-07-11
-- updated on 2026-08-18

