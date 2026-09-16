import torch.Tensor.Basic
import torch.Tensor.prod


@[main]
private lemma main
  [Zero α]
-- given
  (s : List ℕ) :
-- imply
  (⟨(0 : List.Vector α s.prod)⟩ : Tensor α s) = 0 :=
-- proof
  rfl


-- created on 2025-11-30
