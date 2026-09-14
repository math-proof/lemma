import stdlib.SEq
import sympy.tensor.Basic
import torch.Tensor.permute


@[main, cast]
private lemma main
  {s : List ℕ}
-- given
  (h : s = s')
  (X : Tensor α s)
  (i : Fin s.length)
  (d : ℤ):
-- imply
  (cast (congrArg (Tensor α) h) X).permute ⟨i, by grind⟩ d ≃ X.permute i d := by
-- proof
  aesop


-- created on 2025-12-01
