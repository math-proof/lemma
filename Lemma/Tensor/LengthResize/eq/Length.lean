import Lemma.List.GetSet.eq.Get.of.Ne.GtLength
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.tensor
open List Tensor


@[main]
private lemma main
  [Zero α]
-- given
  (X : Tensor α s)
  (i : Fin s.length) :
-- imply
  (X.resize i (s[0]'(by linarith [i.isLt]))).length = X.length := by
-- proof
  have h_i := i.isLt
  repeat rw [Length.eq.Get_0.of.GtLength_0]
  ·
    if h_i : i = ⟨0, by grind⟩ then
      simp [h_i]
    else
      rw [GetSet.eq.Get.of.Ne.GtLength (by grind)]
      grind
  ·
    grind


-- created on 2026-07-09
