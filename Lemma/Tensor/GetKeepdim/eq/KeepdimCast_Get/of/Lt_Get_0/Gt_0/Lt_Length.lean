import stdlib.SEq
import sympy.tensor.functions
import Lemma.Tensor.LengthKeepdim.eq.Length.of.Gt_0
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.Lt_Length
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Keepdim.as.RepeatUnsqueeze.of.Lt_Length
import Lemma.Tensor.All_SEqGetS.of.SEq
import Lemma.Tensor.Length.eq.Get_0.of.GtLength
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Gt_0.Lt_SubLength
import Lemma.Tensor.GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.List.GetInsertIdx.eq.Get.of.Lt.Le_Length
import Lemma.Tensor.GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Nat.EqAddSub.of.Ge
open Tensor List Bool Nat


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
  rw [GetRepeat.eq.Cast_RepeatGet.of.Lt_Get_0.GtVal_0.fin h_dim] at h
  ·
    have h := SEq.of.SEq_Cast h (h := by
      simp
      congr
      .
        omega
      .
        simp [EqAddSub.of.Ge (by omega : dim ≥ 1)]
    )
    rw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin _ h_dim] at h
    .
      sorry
    .
      rwa [h_get_eraseIdx]
  ·
    rw [GetInsertIdx.eq.Get.of.Lt.Le_Length _ h_dim]
    ·
      rwa [h_get_eraseIdx]
    ·
      rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length h_s]
      omega


-- created on 2025-10-09
