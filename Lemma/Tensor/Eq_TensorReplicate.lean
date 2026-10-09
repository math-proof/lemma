import sympy.Basic
import torch.Tensor


@[path]
private lemma main
  [NatCast α]
-- given
  (r : ℕ) :
-- imply
  (r : Tensor α s) = ⟨List.Vector.replicate s.prod (r : α)⟩ :=
-- proof
  rfl


-- created on 2026-07-08
