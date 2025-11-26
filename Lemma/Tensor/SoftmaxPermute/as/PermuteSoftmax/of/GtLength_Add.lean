import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Int.Lt.of.LtAdd
import Lemma.List.EqPermute__0
import Lemma.List.EraseIdxCons.eq.EraseIdx_Sub_1.of.Gt_0
import Lemma.List.EraseIdxPermute.eq.EraseIdx.of.GtLength_Add
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.List.PermuteCons.eq.Cons_Permute.of.GtLength
import Lemma.Nat.AddAdd
import Lemma.Nat.EqAdd0
import Lemma.Tensor.GetPermute.eq.PermuteGet.of.Lt_Get_0.LtAdd_1Length
import Lemma.Tensor.GetSum.eq.Cast_SumGet.of.Lt_Get_0.Gt_0.GtLength
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.SEqPermute__0
import Lemma.Tensor.SEqSoftmaxS.of.SEq
import Lemma.Tensor.SEqSumS.of.SEq
import Lemma.Tensor.SoftmaxCast.eq.Cast_Softmax.of.Eq
import Lemma.Tensor.SumPermuteHead.as.Sum_0.of.GtLength
import sympy.tensor.functions
open Bool Int List Nat Tensor


@[main]
private lemma main
  [ExpPos α]
  {i d : ℕ}
-- given
  (h : s.length > i + d)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i, by grind⟩ d).softmax (i + d) ≃ (X.softmax i).permute ⟨i, by grind⟩ d := by
-- proof
  induction i generalizing X d s with
  | zero =>
    simp at h
    rw [EqAdd0]
    rw [@Tensor.Permute.eq.Ite]
    simp
    split_ifs with h_d0 h_pos h_s
    ·
      subst h_d0
      simp
      have := SEqPermute__0 (X.softmax 0) ⟨0, h⟩
      apply SEq.symm ∘ SEq.trans this
      apply SEqSoftmaxS.of.SEq
      apply SEq_Cast.of.Eq
      rw [EqPermute__0]
    ·
      rw [SoftmaxCast.eq.Cast_Softmax.of.Eq]
      ·
        apply SEqCast.of.SEq.Eq.Eq
        ·
          rw [Permute.eq.AppendRotateTake___Drop.of.GtLength_0]
        ·
          simp
        ·
          rw [@Tensor.Permute.eq.Ite]
          simp
          split_ifs
          apply SEq_Cast.of.SEq.Eq.Eq
          .
            rw [List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
          .
            sorry
          .
            -- apply SoftmaxPermuteHead.as.PermuteHeadSoftmax.of.GtLength h X
            sorry
      ·
        rw [Permute.eq.AppendRotateTake___Drop.of.GtLength_0]
    ·
      omega
    ·
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
      sorry


-- created on 2025-10-31
