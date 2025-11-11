import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Cons_EraseIdxTail.eq.EraseIdx.of.GtLength_0
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.GetSelect.as.Get.of.Lt.Lt_Get_0.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.Select_0.eq.Cast_Get.of.Lt_Get_0.GtLength_0
import Lemma.Vector.EqUnflattenFlatten
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten.of.Lt
import sympy.tensor.tensor
open Bool List Tensor Vector


@[main]
private lemma main
-- given
  (h_d : d < s.length)
  (h_i : i < s[d])
  (h_j : j < n)
  (X : Tensor α (n :: s)) :
-- imply
  have h_length := Length.eq.Get_0.of.GtLength_0 (by simp) X
  (X.select ⟨d + 1, by simpa⟩ ⟨i, by simpa⟩).get ⟨j, by rw [LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0 (by simp) (by simpa) (by simpa)]; simpa⟩ ≃ (X.get ⟨j, by simpa [h_length]⟩).select ⟨d, by simpa⟩ ⟨i, by simpa⟩ := by
-- proof
  simp
  if h_d : d = 0 then
    subst h_d
    simp
    rw [Select_0.eq.Cast_Get.of.Lt_Get_0.GtLength_0 h_d h_i]
    apply SEq_Cast.of.SEq.Eq (by simp)
    apply GetSelect.as.Get.of.Lt.Lt_Get_0.GtLength_0 h_d h_i h_j
  else
    unfold Tensor.get
    simp
    unfold toVector
    simp
    simp only [GetElem.getElem]
    repeat rw [GetCast.eq.Get.of.Eq.fin (by simp)]
    repeat rw [GetMap.eq.UFnGet.of.Lt.fin]
    apply SEq.of.SEqDataS.Eq <;>
      simp
    repeat rw [GetSplitAt_1.eq.GetUnflatten.of.Lt.fin h_j]
    unfold select
    simp [DataFromVector.eq.FlattenMapData]
    simp [EqUnflattenFlatten]
    simp [h_d]
    have h_cons := Cons_EraseIdxTail.eq.EraseIdx.of.GtLength_0.headD (by omega) (by omega) (s := s) (i := d) 1
    rw [DataCast.eq.Cast_Data.of.Eq h_cons]
    apply SEq_Cast.of.SEq.Eq
    ·
      rw [h_cons]
    ·
      -- rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (by grind) (X.toVector.get ⟨j, by grind⟩) ⟨i, by grind⟩]
      sorry


-- created on 2025-11-07
