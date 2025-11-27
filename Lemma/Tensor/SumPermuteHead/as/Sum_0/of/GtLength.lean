import Lemma.Tensor.GetSum_0.as.SumSelect.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetPermuteHead.as.PermuteHeadSelect.of.Lt_Get_1.GtLength_1
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Tensor.GetSum.eq.Cast_SumGet.of.Lt_Get_0.Gt_0.GtLength
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.SEqPermuteHead_1
import Lemma.Tensor.SEqSumS.of.SEq
open Bool List Nat Tensor


@[main]
private lemma main
  [AddCommMonoid α]
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
        have h_t := t.isLt
        simp [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength h_d1] at h_t
        rw [GetAppend.eq.Get.of.GtLength (by simpa)] at h_t
        rw [GetTake.eq.Get.of.Lt_LengthTake (by simpa)] at h_t
        rw [GetSum.eq.Cast_SumGet.of.Lt_Get_0.Gt_0.GtLength.fin]
        ·
          simp
          apply SEqCast.of.SEq.Eq
          ·
            simp
            rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1]
            simp
            rw [EqMin.of.Le h_d]
            rwa [EqAdd_Sub.of.Ge h_d]
          ·
            have := Tensor.GetPermuteHead.as.PermuteHeadSelect.of.Lt_Get_1.GtLength_1 (by simpa) (by simpa) X (d := d + 1) (k := t)
            have := Tensor.SEqSumS.of.SEq this d
            apply SEq.trans this
            have h_length : ((s₀ :: s).eraseIdx 1).length > d := by
              simp
              rwa [EqAddSub.of.Ge (Nat.Ge_1.of.Gt_0 h_s)]
            have ih := ih h_length (X.select ⟨1, by simpa⟩ ⟨t, by simpa⟩)
            apply SEq.trans ih
            .
              apply Tensor.SumSelect.as.GetSum_0.of.Lt_Get_0.GtLength_0 _ h_t
              simp
              rw [List.LengthEraseIdx.eq.SubLength_1.of.GtLength (by simp; omega)]
              simp
              left
              exact h_s
            .
              simp
              rw [List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by omega)]
              simp [EqMin.of.Le h_d]
        ·
          simp [EqMin.of.Le h_d]
        ·
          simp
        ·
          simp
          rw [GetAppend.eq.Get.of.GtLength (by simpa)]
          rwa [GetTake.eq.Get.of.Lt_LengthTake (by simpa)]


-- created on 2025-10-31
-- updated on 2025-11-01
