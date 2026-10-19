import torch.Tensor.Basic
import torch.Tensor.item
open Vector


@[path]
private lemma main
  [One α] :
-- imply
  (1 : Tensor α []).item = 1 :=
-- proof
  EqGet1_1.fin ⟨0, Nat.zero_lt_one⟩


-- created on 2026-09-07
