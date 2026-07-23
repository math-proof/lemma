import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqSwap_0'1
import Lemma.List.Swap.eq.Permute__Neg1.of.GtLength
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetPermuteTail.as.Select.of.GtGet.GtLength_0
import Lemma.Tensor.GetPermute__Neg.as.Select.of.GtGet.GtLength_0
import Lemma.Tensor.Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1
import Lemma.Tensor.T.as.Permute__Neg1.of.GtLength_0
open Bool List Tensor


@[main]
private lemma main
-- given
  (X : Tensor α [m, n])
  (i : Fin n) :
-- imply
  Xᵀ.get i = X.select ⟨1, by grind⟩ i := by
-- proof
  rw [T.eq.Cast_Permute__Neg1.of.GtLength_0 (by grind)]
  have h_swap := Swap.eq.Permute__Neg1.of.GtLength (s := [m, n]) (i := 0) (by grind)
  have h_swap' := h_swap
  simp [EqSwap_0'1] at h_swap
  erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by simp) (by simp; grind) (i := ⟨i, by simp; grind⟩)]
  apply EqCast.of.SEq
  erw [GetPermute__Neg.eq.Cast_Select.of.GtGet.GtLength_0 (by grind) (by simp)]
  apply SEqCast.of.SEq.Eq (by simp; grind)
  rfl


-- created on 2026-07-23
