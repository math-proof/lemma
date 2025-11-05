import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Vector.EqGetS.of.Eq.Lt
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Vector.EqUnflattenFlatten
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.GetEllipsis_0.eq.Cast_Get.of.GtLength_0.Lt_Get_0
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthGet.eq.Get_0.of.Lt_Get_0.GtLength_1
import Lemma.Tensor.LengthGetEllipsis.eq.Get_0.of.Lt_Get.GtLength.Gt_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten.of.Lt
import sympy.tensor.tensor
open List Tensor Vector Bool


@[main]
private lemma main
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (h_j : j < n)
  (X : Tensor α (n :: s)) :
-- imply
  (X.getEllipsis ⟨1, by grind⟩ ⟨i, by grind⟩).get ⟨j, by simp [LengthGetEllipsis.eq.Get_0.of.Lt_Get.GtLength.Gt_0]; grind⟩ ≃ (X.get ⟨j, by simpa [Length.eq.Get_0.of.GtLength_0]⟩).get ⟨i, by simp_all [LengthGet.eq.Get_0.of.Lt_Get_0.GtLength_1]⟩ := by
-- proof
  unfold Tensor.get
  simp
  unfold toVector
  simp
  simp only [GetElem.getElem]
  repeat rw [GetCast.eq.Get.of.Eq.fin]
  ·
    repeat rw [GetMap.eq.UFnGet.of.Lt]
    apply SEq.of.SEqDataS.Eq <;>
      simp
    apply SEq_Cast.of.SEq.Eq
    ·
      simp
    ·
      simp only [GetElem.getElem]
      rw [GetSplitAt_1.eq.GetUnflatten.of.Lt.fin h_j]
      unfold getEllipsis
      simp [DataFromVector.eq.FlattenMapData]
      simp [EqUnflattenFlatten]
      rw [GetEllipsis_0.eq.Cast_Get.of.GtLength_0.Lt_Get_0]
      rw [DataCast.eq.Cast_Data.of.Eq (by simp)]
      apply SEqCast.of.SEq.Eq
      .
        simp
      .
        rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (by grind) (X.toVector.get ⟨j, by grind⟩) ⟨i, by grind⟩]
        apply SEqCast.of.SEq.Eq
        .
          simp
        .
          simp
          apply SEq.of.Eq
          apply EqGetS.of.Eq.Lt
          congr
          simp
          rw [GetToVector.eq.Get.fin (i := ⟨j, by simpa [Length.eq.Get_0.of.Ne_Nil]⟩)]
          rw [GetVal.eq.Get.of.Lt (by simp; grind)]
          apply Eq.of.EqDataS
          simp
          rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨j, by grind⟩) (by simp)]
          apply EqCast.of.SEq
          simp
          apply SEq.of.Eq
          simp [GetElem.getElem]
  ·
    simp
  ·
    apply ProdTake_1.eq.HeadD_1
  ·
    simp


-- created on 2025-11-01
