import Lemma.Tensor.LengthKeepdim.eq.Length.of.Gt_0
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.Lt_Length
import Lemma.List.GetTail.eq.Get_Add_1.of.Lt_LengthTail
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Keepdim.as.RepeatUnsqueeze.of.Lt_Length
import Lemma.Tensor.All_SEqGetS.of.SEq
import Lemma.Tensor.RepeatCast.eq.Cast_Repeat.of.Eq
import Lemma.Tensor.Length.eq.Get_0.of.GtLength
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Gt_0.Lt_SubLength
import Lemma.List.TailInsertIdx.eq.InsertIdxTail.of.Gt_0.GtLength_0
import Lemma.Tensor.GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.List.GetInsertIdx.eq.Get.of.Lt.Le_Length
import Lemma.Tensor.GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.Lt_Length
import Lemma.Bool.Eq.of.SEq.SEq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.EqSetInsertIdxEraseIdx.of.Eq_Get.Lt_Length
import Lemma.List.EqSetInsertIdxEraseIdx.of.Lt_Length
import Lemma.List.TailSet.eq.SetTail.of.Gt_0
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Tensor.UnsqueezeCast.eq.CastUnsqueeze.of.Eq
import Lemma.Tensor.Repeat.as.RepeatCast.of.Eq
import Lemma.Tensor.SEqRepeatS.of.SEq.EqValS.Eq.Eq
open Tensor List Nat Bool


@[main]
private lemma main
  {dim i : ℕ}
  {s : List ℕ}
-- given
  (h_s : dim < s.length)
  (h_dim : dim > 0)
  (h_i : i < s[0])
  (X : Tensor α (s.eraseIdx dim)) :
-- imply
  X.keepdim.get ⟨i, by rwa [LengthKeepdim.eq.Length.of.Gt_0 h_dim X, Length.eq.Get_0.of.GtLength_0, GetEraseIdx.eq.Get.of.Lt.Lt_Length h_s h_dim]⟩ = (cast
    (congrArg (Tensor α) (TailEraseIdx.eq.EraseIdxTail.of.Gt_0.Lt_SubLength h_s h_dim))
    (X.get ⟨i, by
      rw [Length.eq.Get_0.of.GtLength_0]
      rwa [GetEraseIdx.eq.Get.of.Lt.Lt_Length h_s h_dim]⟩)).keepdim := by
-- proof
  have h_get_eraseIdx := GetEraseIdx.eq.Get.of.Lt.Lt_Length h_s h_dim
  have h := Keepdim.as.RepeatUnsqueeze.of.Lt_Length h_s X
  have h := All_SEqGetS.of.SEq h ⟨i, by rwa [Length.eq.Get_0.of.GtLength h_s]⟩
  have h_dim_add_sub := EqAddSub.of.Ge (by omega : dim ≥ 1)
  rw [GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin h_dim] at h
  ·
    rw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin _ h_dim] at h
    ·
      have h_length_pos : (s.eraseIdx dim).length > 0 := by
        rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length h_s]
        omega
      have h_tail := InsertIdxTail.eq.TailInsertIdx.of.Gt_0.GtLength_0 h_length_pos h_dim 1
      have h_i : i < X.length := by
        rw [Length.eq.Get_0.of.GtLength h_length_pos]
        rwa [GetEraseIdx.eq.Get.of.Lt.Lt_Length h_s h_dim]
      have h_lt_length_tail : dim - 1 < s.tail.length := by
        simp
        omega
      have h_d : dim - 1 < ((s.eraseIdx dim).tail.insertIdx (dim - 1) 1).length := by
        rw [TailEraseIdx.eq.EraseIdxTail.of.Gt_0.Lt_SubLength h_s h_dim]
        apply Lt_LengthInsertIdxEraseIdx.of.Lt_Length h_lt_length_tail
      rw [RepeatCast.eq.Cast_Repeat.of.Eq h_tail ((X.get ⟨i, h_i⟩).unsqueeze (dim - 1)) s[dim] ⟨dim - 1, h_d⟩] at h
      apply Eq.of.SEq.SEq h
      apply SEqCast.of.SEq.Eq.Eq
      ·
        rw [EqSetInsertIdxEraseIdx.of.Eq_Get.Lt_Length (by simpa) (by simp)]
        congr
        simp [EqAddSub.of.Ge (by omega : dim ≥ 1)]
        rw [EqSetInsertIdxEraseIdx.of.Lt_Length]
      ·
        congr
        rw [EqSetInsertIdxEraseIdx.of.Eq_Get.Lt_Length h_s]
        simp
      ·
        have h_eq := TailEraseIdx.eq.EraseIdxTail.of.Gt_0.Lt_SubLength h_s h_dim
        have h := Keepdim.as.RepeatUnsqueeze.of.Lt_Length h_lt_length_tail (cast (congrArg (Tensor α) h_eq) (X.get ⟨i, h_i⟩))
        apply SEq.of.SEq.SEq _ h
        have h_get_tail := GetTail.eq.Get_Add_1.of.Lt_LengthTail h_lt_length_tail
        rw [h_get_tail]
        rw [UnsqueezeCast.eq.CastUnsqueeze.of.Eq h_eq]
        have h_s : (s.eraseIdx dim).tail.insertIdx (dim - 1) 1 = (s.tail.eraseIdx (dim - 1)).insertIdx (dim - 1) 1 := by
          simp_all
        have := Repeat.as.RepeatCast.of.Eq h_s ((X.get ⟨i, h_i⟩).unsqueeze (dim - 1)) s[dim - 1 + 1] ⟨dim - 1, h_d⟩
        apply SEq.of.SEq.SEq _ this.symm
        have h_tail_set : ((s.eraseIdx dim).tail.insertIdx (dim - 1) 1).set (dim - 1) s[dim] = (((s.eraseIdx dim).insertIdx dim 1).set dim s[dim]).tail := by
          rw [TailSet.eq.SetTail.of.Gt_0 h_dim]
          rw [TailInsertIdx.eq.InsertIdxTail.of.Gt_0.GtLength_0 h_length_pos h_dim]
        apply SEqCast.of.SEq.Eq.Eq
        repeat simpa [h_dim_add_sub]
        apply SEqRepeatS.of.SEq.EqValS.Eq.Eq (by rfl) _ (by rfl) (by rfl)
        simp [h_dim_add_sub]
    ·
      rwa [h_get_eraseIdx]
  ·
    rw [GetInsertIdx.eq.Get.of.Lt.Le_Length _ h_dim]
    ·
      rwa [h_get_eraseIdx]
    ·
      rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length h_s]
      omega


-- created on 2025-10-09
-- updated on 2025-10-11
