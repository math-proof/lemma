import sympy.tensor.Basic
import torch.Tensor.prod
import torch.Tensor.reshape


@[main, comm]
private lemma main
  {s s' sᵣ : List ℕ}
-- given
  (h_s : s = s')
  (h : s.prod ∣ sᵣ.prod)
  (X : Tensor α s) :
-- imply
  (cast (congrArg (Tensor α) h_s) X).reshape sᵣ (h_s ▸ h) = X.reshape sᵣ h := by
-- proof
  subst h_s
  rfl


-- created on 2026-07-17
