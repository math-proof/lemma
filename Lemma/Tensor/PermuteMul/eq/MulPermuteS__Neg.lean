import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EqPermute__0
import Lemma.List.GetPermute__Neg.eq.Get_0.of.Gt
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.Tensor.Cast_Mul.eq.MulCastS.of.Eq
import Lemma.Tensor.Eq.is.All_EqGetS.of.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetPermute__Neg.as.Permute__Neg_Get.of.Lt_Get_0.LtAdd_1Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.PermuteHeadMul.eq.MulPermuteHeadS
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqPermute__0
open Bool List Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (h_i : s.length > i + d)
  (A B : Tensor α s) :
-- imply
  (A * B).permute ⟨i + d, h_i⟩ (-d) = A.permute ⟨i + d, h_i⟩ (-d) * B.permute ⟨i + d, h_i⟩ (-d) := by
-- proof
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
      apply SEq.symm ∘ SEq.trans h_A_mul_B
      have h_s := Eq_Permute__0 ⟨0, h_i⟩
      rw [Cast_Mul.eq.MulCastS.of.Eq h_s]
      apply SEq.of.EqCast.Eq (h := h_s)
      rw [Cast_Mul.eq.MulCastS.of.Eq h_s]
    ·
      simp [@Tensor.Permute.eq.Ite]
      split_ifs
      sorry
    -- rw [PermuteHeadMul.eq.MulPermuteHeadS]
    -- rw [Cast_Mul.eq.MulCastS.of.Eq]
    -- rw [Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
    ·
      sorry
    -- omega
    ·
      sorry
  -- omega
  | succ i ih =>
    apply Eq.of.All_EqGetS.GtLength_0 (h := by simp; omega)
    intro t
    have h_t := t.isLt
    rw [GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0.fin _ h_t]
    simp [GetPermute__Neg.eq.Get_0.of.Gt (by simp) (d := d) (s := s) (i := ⟨i + 1 + d, h_i⟩)] at h_t
    have h_all := GetPermute__Neg.as.Permute__Neg_Get.of.Lt_Get_0.LtAdd_1Length (s := s) (i := i + d) (k := t) (by grind) h_t (d := d) (α := α) (by grind)
    have h_A := h_all A
    have h_B := h_all B
    have h_A_mul_B := SEqMulS.of.SEq.SEq h_A h_B
    -- rw [show i + d + 1 = i + 1 + d by omega] at h_A_mul_B
    apply Eq.of.SEq
    apply SEq.symm ∘ SEq.trans h_A_mul_B
    rw [← ih (s := s.tail) (by grind) (A.get ⟨t, by grind⟩) (B.get ⟨t, by grind⟩) d (by grind)]
    have h_AB := h_all (A * B)
    simp [GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0.fin _ h_t] at h_AB
    exact h_AB.symm


-- created on 2025-12-02
