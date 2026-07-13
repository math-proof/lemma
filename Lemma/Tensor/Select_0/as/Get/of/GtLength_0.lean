import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Select_0.as.Get.of.GtGet_0.GtLength_0
open Tensor


@[main, cast]
private lemma main
-- given
  (h_s : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  X.select ⟨0, h_s⟩ i ≃ X.get ⟨i, by simp [Length.eq.Get_0.of.GtLength_0 h_s]⟩ := by
-- proof
  apply Select_0.as.Get.of.GtGet_0.GtLength_0


-- created on 2025-11-07
