import Lemma.List.GetPermute__Neg.eq.Get
import Lemma.List.Permute__Neg.eq.Cons_EraseIdx
import Lemma.Tensor.Cast_Mul.eq.MulCastS.of.Eq
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.PermuteMul.eq.MulPermuteS
import Lemma.Tensor.Select.eq.Cast_GetPermute
open List Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (A B : Tensor α s)
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (A * B).select d i = A.select d i * B.select d i := by
-- proof
  simp [Select.eq.Cast_GetPermute]
  have h_s := Permute__Neg.eq.Cons_EraseIdx d
  have h_i := i.isLt
  repeat rw [← GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp; grind) h_s _ ⟨i, by rwa [GetPermute__Neg.eq.Get]⟩ (s' := (s[d] :: s.eraseIdx d))]
  simp
  have h_all := GetMul.eq.MulGetS.of.Lt_Get_0.GtLength_0.fin (s := s[d] :: s.eraseIdx d) (i := i) (by simp) (by simp) (α := α)
  simp at h_all
  simp [← h_all]
  congr
  rw [PermuteMul.eq.MulPermuteS]
  apply Cast_Mul.eq.MulCastS.of.Eq h_s


-- created on 2025-12-01
