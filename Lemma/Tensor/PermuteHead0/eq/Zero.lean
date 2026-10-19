import torch.Tensor.permute
import Lemma.Tensor.EqTensor0'0
import Lemma.Tensor.Rotate0.eq.Zero
open Tensor Vector


@[path]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (size : ℕ) :
-- imply
  (0 : Tensor α s).permuteHead size = 0 := by
-- proof
  apply Eq.of.EqDataS
  simp [Tensor.permuteHead, EqData0'0, EqSplitAt0_0,
    EqTensor0'0, Tensor.Rotate0.eq.Zero, Flatten0.eq.Zero]
  rw [EqCast_0'0.of.Eq (by simp [List.prod_append])]


-- created on 2026-09-16
