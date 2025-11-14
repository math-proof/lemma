import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Cons_EraseIdxTail.eq.EraseIdx.of.GtLength_0
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.Nat.EqSubAdd
import Lemma.Nat.LtVal
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.GetSelect.as.Get.of.Lt_Get_0.Lt_Get_1.GtLength_1
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0
import Lemma.Tensor.Lt_Length.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqStack_Get.of.GtLength_0
import Lemma.Tensor.SelectCast.eq.Cast_Select.of.Eq
import Lemma.Tensor.Select_0.eq.Cast_Get.of.Lt_Get_0.GtLength_0
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import sympy.tensor.tensor
open Vector Tensor Bool List Nat


@[main]
private lemma main
-- given
  (h_d : d + 1 < s.length)
  (h_i : i < s[d + 1])
  (h_j : j < s[0])
  (X : Tensor α s) :
-- imply
  have h_length := Length.eq.Get_0.of.GtLength_0 (by omega) X
  (X.select ⟨d + 1, h_d⟩ ⟨i, by simpa⟩).get ⟨j, by rw [LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0 (by simp) (by simpa) (by simpa)]; simpa⟩ ≃ (X.get ⟨j, by simpa [h_length]⟩).select ⟨d, by grind⟩ ⟨i, by simpa⟩ := by
-- proof
  simp
  induction d generalizing s X i j with
  | zero =>
    simp
    rw [Select_0.eq.Cast_Get.of.Lt_Get_0.GtLength_0 (by grind) (by grind)]
    apply SEq_Cast.of.SEq.Eq (by simp)
    apply GetSelect.as.Get.of.Lt_Get_0.Lt_Get_1.GtLength_1 (by grind) h_i h_j
  | succ d ih =>
    unfold Tensor.get
    simp
    unfold toVector
    simp only [GetElem.getElem]
    repeat rw [GetCast.eq.Get.of.Eq.fin (by rw [ProdTake_1.eq.HeadD_1])]
    repeat rw [GetMap.eq.UFnGet.of.Lt.fin]
    apply SEq.of.SEqDataS.Eq
    ·
      rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1]
      omega
    ·
      simp
      apply SEqCast.of.SEq.Eq (by simp)
      have h_X := SEqStack_Get.of.GtLength_0 (by omega) X
      have h_X := EqCast.of.SEq h_X
      conv_lhs => rw [← h_X]
      have h_s := EqCons_Tail.of.GtLength_0 (s := s) (by omega)
      have := SelectCast.eq.Cast_Select.of.Eq h_s (([i < s[0]] (X[i]'(Lt_Length.of.GtLength_0 (by omega) X i)))) ⟨d + 1 + 1, by simp; grind⟩ ⟨i, by grind⟩
      simp at this
      simp [this]
      rw [DataCast.eq.Cast_Data.of.Eq (by grind)]
      unfold select
      simp [DataFromVector.eq.FlattenMapData]
      have h_cons := Cons_EraseIdxTail.eq.EraseIdx.of.GtLength_0.headD (by grind) (by omega) (s := s.tail) (i := d + 1) 1
      rw [EqSubAdd] at h_cons
      rw [DataCast.eq.Cast_Data.of.Eq h_cons]
      apply SEq_Cast.of.SEq.Eq (by grind)
      apply SEq.of.All_EqGetS.Eq.fin (by grind)
      simp
      intro t
      have h_t := LtVal t
      rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
      rw [DataFromVector.eq.FlattenMapData]
      sorry


-- created on 2025-11-07
-- updated on 2025-11-14
