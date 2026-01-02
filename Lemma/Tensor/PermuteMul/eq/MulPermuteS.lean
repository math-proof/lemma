import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EqPermute__0
import Lemma.List.GetPermute.eq.Get.of.Gt
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.Nat.Gt_0
import Lemma.Tensor.Cast_Mul.eq.MulCastS.of.Eq
import Lemma.Tensor.Eq.is.All_EqGetS.of.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetPermute.as.PermuteGet.of.Lt_Get_0.LtAdd_1Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.PermuteHeadMul.eq.MulPermuteHeadS
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqPermute__0
open Bool List Nat Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (h_i : s.length > i)
  (A B : Tensor α s)
  (d : ℕ) :
-- imply
  (A * B).permute ⟨i, h_i⟩ d = A.permute ⟨i, h_i⟩ d * B.permute ⟨i, h_i⟩ d := by
-- proof
  have h_s := Gt_0 ⟨i, h_i⟩
  induction i generalizing s A B d with
  | zero =>
    rw [@Tensor.Permute.eq.Ite]
    simp
    split_ifs with h_d h_d h_d
    ·
      subst h_d
      have h_all := SEqPermute__0 (i := ⟨0, h_i⟩) (s := s) (α := α)
      have h_A := h_all A
      have h_B := h_all B
      have h_A_mul_B := SEqMulS.of.SEq.SEq h_A h_B
      apply Eq.of.SEq
      symm
      apply h_A_mul_B.trans
      have h_s := Eq_Permute__0 ⟨0, h_i⟩
      rw [Cast_Mul.eq.MulCastS.of.Eq h_s]
      apply SEq.of.EqCast.Eq (h := h_s)
      rw [Cast_Mul.eq.MulCastS.of.Eq h_s]
    ·
      simp [@Tensor.Permute.eq.Ite]
      split_ifs
      rw [PermuteHeadMul.eq.MulPermuteHeadS]
      rw [Cast_Mul.eq.MulCastS.of.Eq]
      rw [Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
    ·
      omega
    ·
      omega
  | succ i ih =>
    apply Eq.of.All_EqGetS.GtLength_0 (h := by simpa)
    intro t
    have h_t := t.isLt
    rw [GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0.fin _ h_t]
    simp [GetPermute.eq.Get.of.Gt (by simp) d (s := s) (i := ⟨i + 1, h_i⟩) (j := 0)] at h_t
    have h_all := GetPermute.as.PermuteGet.of.Lt_Get_0.LtAdd_1Length (s := s) (i := i) (k := t) h_i h_t (d := d) (α := α)
    have h_A := h_all A
    have h_B := h_all B
    have h_A_mul_B := SEqMulS.of.SEq.SEq h_A h_B
    apply Eq.of.SEq
    symm
    apply h_A_mul_B.trans
    rw [← ih (s := s.tail) (by grind) (A.get ⟨t, by grind⟩) (B.get ⟨t, by grind⟩) d (by grind)]
    have h_AB := h_all (A * B)
    simp [GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0.fin _ h_t] at h_AB
    exact h_AB.symm


-- created on 2025-12-01
-- updated on 2025-12-02
