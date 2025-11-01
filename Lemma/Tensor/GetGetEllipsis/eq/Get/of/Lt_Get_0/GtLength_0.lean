import Lemma.Tensor.DataGet.eq.GetUnflattenData
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
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
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
  unfold Tensor.toVector
  simp
  repeat rw [@Vector.GetCast.eq.Get.of.Eq.Lt]
  ·
    repeat rw [GetMap.eq.UFnGet.of.Lt]
    apply SEq.of.SEqDataS.Eq <;>
      simp
    apply SEq_Cast.of.SEq.Eq
    ·
      simp
    ·
      simp only [GetElem.getElem]
      -- have h_prod : i < (s.take 1).prod := by
        -- rwa [ProdTake_1.eq.Get_0.of.GtLength_0]
      rw [GetSplitAt_1.eq.GetUnflatten.of.Lt.fin h_j]
      -- unfold List.Vector.splitAt
      unfold Tensor.getEllipsis
      simp [DataFromVector.eq.FlattenMapData]
      -- rw [GetSplitAt_1.eq.GetUnflatten.of.Lt.fin h_j]
      simp [EqUnflattenFlatten]
      rw [GetEllipsis_0.eq.Cast_Get.of.GtLength_0.Lt_Get_0]
      rw [Tensor.DataCast.eq.Cast_Data.of.Eq (by simp)]
      apply SEqCast.of.SEq.Eq
      .
        simp
      .
        -- simp [DataGet.eq.GetUnflattenData.fin]
        sorry
  ·
    simpa
  ·
    simp
  ·
    rwa [ProdTake_1.eq.Get_0.of.GtLength_0 (by omega)]
  ·
    apply ProdTake_1.eq.HeadD_1
  ·
    simpa
  ·
    simp


-- created on 2025-11-01
