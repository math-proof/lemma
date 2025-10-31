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
    split_ifs with h_d0 h_pos? h_i0
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
      -- apply SEq.of.All_SEqGetS.Eq
      simp at h
      rw [AddAdd.comm] at h
      simp at h
      sorry


-- created on 2025-10-31
