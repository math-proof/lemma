import Lemma.List.TailTail.eq.TailEraseIdx_1
import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.GetSelect_1.as.Get.of.Lt_Get_0.Lt_Get_1.GtLength_1
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthGet.eq.Get_0.of.Lt_Get_0.GtLength_1
import Lemma.Tensor.LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0
open Bool Tensor


@[main]
private lemma main
-- given
  (h_s : s.length > 1)
  (h_i : i < s[1])
  (h_j : j < s[0])
  (X : Tensor α s) :
-- imply
  (X.select ⟨1, by grind⟩ ⟨i, by grind⟩).get ⟨j, by simp [LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0]; grind⟩ = cast (congrArg (Tensor α) (List.TailTail.eq.TailEraseIdx_1 s)) ((X.get ⟨j, by rwa [Length.eq.Get_0.of.GtLength_0]⟩).get ⟨i, by simp_all [LengthGet.eq.Get_0.of.Lt_Get_0.GtLength_1]⟩) := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetSelect_1.as.Get.of.Lt_Get_0.Lt_Get_1.GtLength_1 h_s h_i h_j


-- created on 2026-01-13
