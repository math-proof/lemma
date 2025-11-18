import Lemma.Tensor.SelectSoftmax.eq.SoftmaxSelect.of.Lt
import Lemma.Tensor.SEqPermuteHeadS.of.SEq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.Ge_Length
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.GetAppend.eq.Get.of.Lt_Length
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Tensor.GetPermuteHead.as.PermuteHeadSelect.of.Lt_Get_1.GtLength_1
import Lemma.Tensor.GetSoftmax.eq.SoftmaxGet.of.Lt_Get_0.Gt_0.Lt_Length
import Lemma.Tensor.GetSum_0.as.SumSelect.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.SEqPermuteHead_1
import Lemma.Tensor.SEqSoftmaxS.of.SEq
import Lemma.Tensor.SEqSumS.of.SEq
import sympy.tensor.functions
open Bool List Nat Tensor
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [ExpPos α]
  {d : ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α s) :
-- imply
  (X.permuteHead (d + 1)).softmax d ≃ (X.softmax 0).permuteHead (d + 1) := by
-- proof
  induction d generalizing X s with
  | zero =>
    simp
    have := SEqPermuteHead_1 (X.softmax 0)
    apply SEq.symm ∘ SEq.trans this
    apply SEqSoftmaxS.of.SEq
    apply SEq_PermuteHead_1
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
        simp at h_t
        rw [GetAppend.eq.Get.of.Lt_Length (by simpa)] at h_t
        rw [GetTake.eq.Get.of.Lt_LengthTake (by simpa)] at h_t
        rw [GetSoftmax.eq.SoftmaxGet.of.Lt_Get_0.Gt_0.Lt_Length.fin]
        ·
          simp
          have := GetPermuteHead.as.PermuteHeadSelect.of.Lt_Get_1.GtLength_1 (by simpa) (by simpa) X (d := d + 1) (k := t)
          have := SEqSoftmaxS.of.SEq this d
          apply SEq.trans this
          have h_length : ((s₀ :: s).eraseIdx 1).length > d := by
            simp
            rwa [EqAddSub.of.Ge (Ge_1.of.Gt_0 h_s)]
          have ih := ih h_length (X.select ⟨1, by simpa⟩ ⟨t, by simpa⟩)
          apply SEq.trans ih
          ·
            have := GetPermuteHead.as.PermuteHeadSelect.of.Lt_Get_1.GtLength_1 (by simpa) (by simpa) (X.softmax 0) (d := d + 1) (k := t)
            apply SEq.symm ∘ SEq.trans this
            apply SEqPermuteHeadS.of.SEq
            apply SEq.of.Eq
            .
              rw [Tensor.SelectSoftmax.eq.SoftmaxSelect.of.Lt]
              simp
            .
              simp
          ·
            simp
        ·
          simp [EqMin.of.Le h_d]
        ·
          simp
        ·
          simp
          rw [GetAppend.eq.Get.of.Lt_Length (show 0 < (s.take (d + 1)).length by simpa)]
          rwa [GetTake.eq.Get.of.Lt_LengthTake (by simpa)]


-- created on 2025-11-17
