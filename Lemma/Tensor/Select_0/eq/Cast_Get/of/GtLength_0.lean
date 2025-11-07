import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Select_0.eq.Cast_Get.of.Lt_Get_0.GtLength_0
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
-- given
  (h_s : s.length > 0)
  (i : Fin s[0])
  (X : Tensor α s) :
-- imply
  X.select ⟨0, h_s⟩ i = cast (by simp) (X.get ⟨i, by simp [Length.eq.Get_0.of.GtLength_0 h_s]⟩) := by
-- proof
  apply Select_0.eq.Cast_Get.of.Lt_Get_0.GtLength_0


-- created on 2025-11-07
