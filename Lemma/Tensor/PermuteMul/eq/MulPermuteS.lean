import Lemma.Bool.SEq.is.Eq
import Lemma.List.GetPermute.eq.Get.of.Gt
import Lemma.Nat.Gt_0
import Lemma.Tensor.Eq.is.All_EqGetS.of.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetPermute.as.PermuteGet.of.Lt_Get_0.LtAdd_1Length
import Lemma.Tensor.SEqMulS.of.SEq.SEq
open List Nat Tensor Bool


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
    sorry
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
    apply SEq.symm ∘ SEq.trans h_A_mul_B
    rw [← ih (s := s.tail) (by grind) (A.get ⟨t, by grind⟩) (B.get ⟨t, by grind⟩) d (by grind)]
    have h_AB := h_all (A * B)
    simp [GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0.fin _ h_t] at h_AB
    exact h_AB.symm


-- created on 2025-12-01
