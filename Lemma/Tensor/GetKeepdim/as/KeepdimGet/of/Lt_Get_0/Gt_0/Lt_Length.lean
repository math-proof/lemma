import stdlib.SEq
import sympy.tensor.functions
import Lemma.Tensor.LengthKeepdim.eq.Length.of.Gt_0
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.Lt_Length
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.List.LengthInsertIdxEraseIdx.eq.Length.of.Lt_Length
import Lemma.Tensor.LengthRepeat.eq.Get_0.of.GtVal_0
import Lemma.List.GetInsertIdx.eq.Get.of.Lt.Le_Length
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.Tensor.Keepdim.eq.Cast_RepeatUnsqueeze.of.Lt_Length
open Tensor List


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
  X.keepdim.get ⟨i, by
    rwa [LengthKeepdim.eq.Length.of.Gt_0 h_dim X, Length.eq.Get_0.of.GtLength_0, GetEraseIdx.eq.Get.of.Lt.Lt_Length h_s h_dim]⟩ ≃ ((X.unsqueeze dim).repeat s[dim] ⟨dim, by
    rwa [LengthInsertIdxEraseIdx.eq.Length.of.Lt_Length h_s]⟩).get ⟨i, by
    rw [LengthRepeat.eq.Get_0.of.GtVal_0 h_dim]
    rw [GetInsertIdx.eq.Get.of.Lt.Le_Length _ h_dim]
    ·
      rwa [GetEraseIdx.eq.Get.of.Lt.Lt_Length h_s h_dim]
    ·
      rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length h_s]
      omega⟩ := by
-- proof
  have h := Keepdim.eq.Cast_RepeatUnsqueeze.of.Lt_Length h_s X
  sorry


-- created on 2025-10-09
