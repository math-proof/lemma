import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.GetAppend.eq.Get.of.Lt_Length
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.LtVal
import Lemma.Tensor.GetSum.eq.Cast_Sum.of.Lt_Get_0.Gt_0.Lt_Length
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.SEqPermuteHead_1
import Lemma.Tensor.SEqSumS.of.SEq
open Bool List Nat Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α s) :
-- imply
  (X.permuteHead (d + 1)).sum d ≃ X.sum 0 := by
-- proof
  induction d generalizing X s with
  | zero =>
    simp
    apply SEqSumS.of.SEq
    apply SEqPermuteHead_1
  | succ d ih =>
    match s with
    | [] =>
      simp at h
    | s₀ :: s =>
      simp at h
      have h_s : s.length > 0 := by omega
      have h_d : d + 1 ≤ s.length := by omega
      have h_d1 : (d + 1) ≥ (s.take (d + 1)).length := by simp
      apply SEq.of.All_SEqGetS.Eq.GtLength_0
      ·
        intro t
        have h_t := LtVal t
        simp [EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length h_d1] at h_t
        rw [GetAppend.eq.Get.of.Lt_Length (by simpa)] at h_t
        rw [GetTake.eq.Get.of.Lt_LengthTake (by simpa)] at h_t
        rw [GetSum.eq.Cast_Sum.of.Lt_Get_0.Gt_0.Lt_Length.fin]
        ·
          simp
          apply SEqCast.of.SEq.Eq.Eq
          ·
            simp
            rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1]
            simp
            rw [EqMin.of.Le h_d]
            rwa [EqAdd_Sub.of.Ge h_d]
          ·
            simp [EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length h_d1]
            simp [EqMin.of.Le h_d]
          ·
            sorry
        ·
          simp [EqMin.of.Le h_d]
        ·
          simp
        ·
          simp
          rw [GetAppend.eq.Get.of.Lt_Length (by simpa)]
          rwa [GetTake.eq.Get.of.Lt_LengthTake (by simpa)]
      ·
        simp
        grind
      ·
        simp
        rw [EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length (by simp)]
        simp
        rw [EqMin.of.Le (by omega)]
        simp


-- created on 2025-10-31
-- updated on 2025-11-01
