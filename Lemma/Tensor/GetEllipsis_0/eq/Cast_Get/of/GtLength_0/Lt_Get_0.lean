import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.GetEllipsis_0.as.Get.of.GtLength_0.Lt_Get_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.tensor
open Bool Tensor


@[main]
private lemma main
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  X.select ⟨0, h_s⟩ ⟨i, by simp_all⟩ = cast (by simp) (X.get ⟨i, by simpa [Length.eq.Get_0.of.GtLength_0 h_s]⟩) := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetEllipsis_0.as.Get.of.GtLength_0.Lt_Get_0 h_s h_i


-- created on 2025-11-01
