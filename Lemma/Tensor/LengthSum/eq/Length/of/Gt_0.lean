import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.EqLength_0.of.Eq_Nil
import Lemma.Tensor.LengthSum.eq.Length.of.Ge_Length
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.Lt_Length
open Tensor List


@[main]
private lemma main
  [Add α] [Zero α]
  {dim : ℕ}
-- given
  (h : dim > 0)
  (X : Tensor α s) :
-- imply
  (X.sum dim).length = X.length := by
-- proof
  if h : s.length > 0 then
    repeat rw [Length.eq.Get_0.of.GtLength_0 (by assumption)]
    if h : dim < s.length then
      repeat rw [Length.eq.Get_0.of.GtLength_0 (by grind)]
      rw [GetEraseIdx.eq.Get.of.Lt.Lt_Length (by assumption) (by assumption)]
    else
      simp at h
      apply LengthSum.eq.Length.of.Ge_Length h
  else
    simp at h
    repeat rw [EqLength_0.of.Eq_Nil]
    ·
      assumption
    ·
      simp_all


-- created on 2025-06-24
