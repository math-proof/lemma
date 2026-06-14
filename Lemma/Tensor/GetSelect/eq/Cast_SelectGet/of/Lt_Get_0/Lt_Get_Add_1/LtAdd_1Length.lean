import Lemma.Bool.EqCast.of.SEq
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.Tensor.GetSelect.as.SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0
open Bool Tensor List


@[main, comm]
private lemma main
-- given
  (h_d : d + 1 < s.length)
  (h_i : i < s[d + 1])
  (h_j : j < s[0])
  (X : Tensor α s) :
-- imply
  (X.select ⟨d + 1, h_d⟩ ⟨i, by simpa⟩).get ⟨j, by rw [LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0 (by simp) (by simpa) (by simpa)]; simpa⟩ =
    cast
      (congrArg (Tensor α) (EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 (by grind)))
      ((X.get ⟨j, by simpa [Length.eq.Get_0.of.GtLength_0 (by omega) X]⟩).select ⟨d, by grind⟩ ⟨i, by simpa⟩) := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetSelect.as.SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length h_d h_i h_j


-- created on 2026-06-14
