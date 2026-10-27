import Lemma.Tensor.DataSum_0.eq.SumSplitAtData
import Def.Data.Holor.Sum
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Sum.of.SEq
import Lemma.Vector.GetCast.eq.Get.of.Eq
open Tensor Vector


@[path, comm]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α [n]) :
-- imply
  (X.sum 0).data.head = X.data.sum := by
-- proof
  rw [DataSum_0.eq.SumSplitAtData]
  simp
  unfold List.Vector.splitAt
  simp
  erw [Head.eq.Get_0.fin]
  erw [GetSum.eq.SumMapGet.fin]
  apply Sum.of.SEq
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro i
    have h_i := i.isLt
    erw [GetMap.eq.UFnGet.fin]
    erw [GetUnflatten.eq.Get_AddMul.fin]
    erw [GetCast.eq.Get.of.Eq.fin (by simp)]
    simp
  ·
    simp


-- created on 2026-04-24
-- updated on 2026-10-26
