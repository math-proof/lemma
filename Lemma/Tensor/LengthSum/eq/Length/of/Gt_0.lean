import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.EqLength_0.of.Eq_Nil
import Lemma.Tensor.LengthSum.eq.Length.of.LeLength
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
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
      rw [GetEraseIdx.eq.Get.of.Gt.GtLength (by assumption) (by assumption)]
    else
      simp at h
      apply LengthSum.eq.Length.of.LeLength h
  else
    simp at h
    repeat rw [EqLength_0.of.Eq_Nil]
    ·
      assumption
    ·
      simp_all


-- created on 2025-06-24
