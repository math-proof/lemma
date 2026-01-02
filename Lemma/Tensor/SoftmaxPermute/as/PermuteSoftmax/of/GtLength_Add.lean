import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.EqPermute__0
import Lemma.List.GetPermute.eq.Get.of.Gt
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.Nat.AddAdd
import Lemma.Nat.EqAdd0
import Lemma.Tensor.GetPermute.as.PermuteGet.of.Lt_Get_0.LtAdd_1Length
import Lemma.Tensor.GetSoftmax.eq.SoftmaxGet.of.Lt_Get_0.Gt_0.GtLength
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.SEqPermute__0
import Lemma.Tensor.SEqSoftmaxS.of.SEq
import Lemma.Tensor.SoftmaxCast.eq.Cast_Softmax.of.Eq
import Lemma.Tensor.SoftmaxPermuteHead.as.PermuteHeadSoftmax.of.GtLength
import sympy.tensor.functions
open Bool List Nat Tensor


/--
similar with Tensor.SumPermute.as.PermuteSum.of.GtLength_Add
-/
@[main]
private lemma main
  [Exp α]
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
      symm
      apply this.trans
      apply SEqSoftmaxS.of.SEq
      apply SEq_Cast.of.Eq
      rw [EqPermute__0]
    ·
      rw [SoftmaxCast.eq.Cast_Softmax.of.Eq]
      ·
        apply SEqCast.of.SEq.Eq
        ·
          rw [Permute.eq.AppendRotateTake___Drop.of.GtLength_0]
        ·
          rw [@Tensor.Permute.eq.Ite]
          simp
          split_ifs
          apply SEq_Cast.of.SEq.Eq
          ·
            rw [Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
          ·
            apply SoftmaxPermuteHead.as.PermuteHeadSoftmax.of.GtLength h X
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
      apply SEq.of.All_SEqGetS.Eq.GtLength_0 (by simp) (by simp)
      intro t
      have h_t := t.isLt
      simp [GetPermute.eq.Get.of.Gt (by simp) d (s := s₀ :: s) (i := ⟨i + 1, by omega⟩) (j := 0)] at h_t
      rw [GetSoftmax.eq.SoftmaxGet.of.Lt_Get_0.Gt_0.GtLength.fin (by simp; omega) (by simp) (by simp)]
      simp
      have := GetPermute.as.PermuteGet.of.Lt_Get_0.LtAdd_1Length (i := i) (by simp; omega) h_t X d
      have := SEqSoftmaxS.of.SEq this (i + d)
      apply this.trans
      have ih := ih h (X.get ⟨t, by grind⟩)
      apply ih.trans
      have := GetPermute.as.PermuteGet.of.Lt_Get_0.LtAdd_1Length (i := i) (by simp; omega) h_t (X.softmax (i + 1)) d
      symm
      apply this.trans
      rw [GetSoftmax.eq.SoftmaxGet.of.Lt_Get_0.Gt_0.GtLength.fin (by simp; omega) (by simp) (by simpa)]
      rfl


-- created on 2025-10-31
-- updated on 2025-11-30
