import torch.Tensor.permute
import Lemma.Tensor.Transpose0.eq.Zero
open Tensor


@[main]
private lemma main
  [Zero α]
  {s : List ℕ} :
-- imply
  (0 : Tensor α s).T = 0 := by
-- proof
  simp [Tensor.T, Transpose0.eq.Zero]


-- created on 2026-09-16
