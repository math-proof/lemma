import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.List.EqSwap.of.LeLength_1
import Lemma.List.Swap.eq.Permute__Neg1.of.GtLength
import Lemma.Nat.AddSub.eq.Sub_Sub.of.Ge.Ge
import Lemma.Tensor.Cast_Mul.eq.MulCastS.of.Eq
import Lemma.Tensor.PermuteMul.eq.MulPermuteS__Neg.of.GtLength_Add
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
import Lemma.Tensor.SEqT.of.LeLength_1
import Lemma.Tensor.T.as.Permute__Neg1.of.GtLength_0
import sympy.tensor.tensor
open Bool List Nat Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (X Y : Tensor α s) :
-- imply
  (X * Y)ᵀ = Xᵀ * Yᵀ := by
-- proof
  if h : s.length ≥ 2 then
    rw [T.eq.Cast_Permute__Neg1.of.GtLength_0 (by grind)]
    conv_rhs => rw [T.eq.Cast_Permute__Neg1.of.GtLength_0 (by grind)]
    conv_rhs =>
      arg 2
      rw [T.eq.Cast_Permute__Neg1.of.GtLength_0 (by grind)]
    have h_permute := Permute__Neg1.eq.Swap.of.GtLength (by simp; grind) (i := s.length - 2) (s := s)
    simp [AddSub.eq.Sub_Sub.of.Ge.Ge h (show 2 ≥ 1 by grind)] at h_permute
    rw [MulCastS.eq.Cast_Mul.of.Eq (by rw [← h_permute])]
    apply EqCastS.of.SEq.Eq h_permute
    have h_permute_mul := PermuteMul.eq.MulPermuteS__Neg.of.GtLength_Add
      (i := s.length - 2)
      (d := 1)
      (by grind)
      X Y
    simp at h_permute_mul
    have h_permute_mul := SEq.of.Eq h_permute_mul
    have h_all : ∀ (A : Tensor α s), A.permute ⟨s.length - 2 + 1, by grind⟩ (-1) ≃ A.permute ⟨s.length - 1, by grind⟩ (-1) := by
      intro A
      apply SEqPermuteS.of.SEq.Eq.Eq.GtLength
      ·
        grind
      ·
        rfl
      ·
        rfl
    apply (h_permute_mul.symm.trans (h_all (X * Y))).symm.trans
    apply SEqMulS.of.SEq.SEq
    repeat apply h_all
  else
    have h : s.length ≤ 1 := by omega
    rw [T.eq.Cast.of.LeLength_1 h]
    conv_rhs => rw [T.eq.Cast.of.LeLength_1 h]
    conv_rhs =>
      arg 2
      rw [T.eq.Cast.of.LeLength_1 h]
    rw [MulCastS.eq.Cast_Mul.of.Eq (by rw [EqSwap.of.LeLength_1 h])]


-- created on 2026-07-22
