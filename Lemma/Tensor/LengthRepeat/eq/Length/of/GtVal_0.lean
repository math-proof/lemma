import Lemma.List.GetSet.eq.Get.of.Ne.GtLength
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.tensor
open List Tensor


@[main]
private lemma main
  {d : Fin s.length}
-- given
  (h : d.val > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat d n).length = X.length := by
-- proof
  repeat rw [Length.eq.Get_0.of.GtLength_0]
  ·
    rw [GetSet.eq.Get.of.Ne.GtLength (by grind)]
    grind
  ·
    grind


-- created on 2026-07-04
