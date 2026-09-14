import Lemma.Tensor.DataSum_0.eq.SumSplitAtData
import torch.Tensor.sum
import torch.Tensor.unsqueeze
import Lemma.Tensor.DataUnsqueeze.as.Data
import Lemma.Vector.Get.of.SEq.Lt
import Lemma.Vector.Sum.eq.Head
open Tensor Vector


@[main]
private lemma main
  [AddZeroClass α]
-- given
  (X : Tensor α s) :
-- imply
  (X.unsqueeze 0).sum 0 = X := by
-- proof
  apply Eq.of.EqDataS
  erw [DataSum_0.eq.SumSplitAtData]
  unfold List.Vector.splitAt
  simp
  erw [Sum.eq.Head]
  rw [Head.eq.Get_0.fin]
  ext i
  rw [GetUnflatten.eq.Get_AddMul.fin]
  simp
  apply Get.of.SEq.Lt.fin
  apply DataUnsqueeze.as.Data


-- created on 2026-07-22
