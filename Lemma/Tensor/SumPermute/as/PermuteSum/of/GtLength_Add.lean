import Lemma.List.EraseIdxCons.eq.EraseIdx_Sub_1.of.Gt_0
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Nat.Lt.of.LtAdd
import Lemma.List.PermuteCons.eq.Cons_Permute.of.GtLength
import Lemma.Tensor.SEqSumS.of.SEq
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.EqPermute__0
import Lemma.List.EraseIdxPermute.eq.Tail.of.GtLength
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.Nat.EqAdd0
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.Tensor.SumCast.as.Sum.of.Eq
import Lemma.Tensor.SumCast.eq.Cast_Sum.of.Eq
import Lemma.Tensor.SumPermuteHead.as.Sum_0.of.GtLength
import sympy.tensor.functions
open Bool List Nat Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {i d : ℕ}
-- given
  (h : s.length > i + d)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i, by grind⟩ d).sum (i + d) ≃ X.sum i := by
-- proof
  induction i generalizing X d s with
  | zero =>
    simp at h
    rw [EqAdd0]
    rw [@Tensor.Permute.eq.Ite]
    simp
    split_ifs with h_d0 h_pos h_s
    .
      subst h_d0
      apply Tensor.SEqSumS.of.SEq
      apply Bool.SEqCast.of.Eq
      simp [List.EqPermute__0]
    .
      rw [SumCast.eq.Cast_Sum.of.Eq]
      .
        apply SEqCast.of.SEq.Eq.Eq
        ·
          rw [Permute.eq.AppendRotateTake___Drop.of.GtLength_0]
        ·
          simp
          rw [EraseIdxPermute.eq.Tail.of.GtLength h]
        ·
          apply SumPermuteHead.as.Sum_0.of.GtLength h X
      .
        rw [Permute.eq.AppendRotateTake___Drop.of.GtLength_0]
    .
      omega
    .
      omega
  | succ i ih =>
    match s with
    | [] =>
      simp at h
    | s₀ :: s =>
      simp at h
      rw [AddAdd.comm] at h
      simp at h
      have h_length_gt : (s₀ :: s).length > i + 1 + d := by omega
      have h_length_gt_i := Lt.of.LtAdd.left h
      apply Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
      .
        intro t
        have h_t := LtVal t
        simp [EraseIdxPermute.eq.EraseIdx.of.GtLength_Add h_length_gt] at h_t
        repeat rw [GetSum.eq.Cast_Sum.of.Lt_Get_0.Gt_0.Lt_Length.fin]
        .
          apply SEqCastS.of.SEq.Eq.Eq
          .
            simp
            rw [PermuteCons.eq.Cons_Permute.of.GtLength h_length_gt_i s₀ d]
            simp
            rw [EraseIdxCons.eq.EraseIdx_Sub_1.of.Gt_0 (by simp)]
            simp
          .
            simp
          .
            rw [show (i + 1 + d - 1) = i + d by simp]
            simp
            sorry
        .
          simpa
        .
          simp
        .
          simpa
        .
          simpa [PermuteCons.eq.Cons_Permute.of.GtLength _ s₀ d]
        .
          simp
        .
          simpa [PermuteCons.eq.Cons_Permute.of.GtLength _ s₀ d]
      .
        rw [List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length (by simp; omega)]
        simp
        omega
      .
        simp
        rw [List.EraseIdxPermute.eq.EraseIdx.of.GtLength_Add h_length_gt]
        simp


-- created on 2025-10-31
