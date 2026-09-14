import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import torch.Tensor.unsqueeze
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.GeLength
import Lemma.List.LengthInsertIdx.eq.Length.of.LtLength
open Tensor List


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  (X.unsqueeze 0).length = 1 := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0]
  aesop


-- created on 2025-10-10
