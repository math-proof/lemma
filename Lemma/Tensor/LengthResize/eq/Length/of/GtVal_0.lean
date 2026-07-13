import Lemma.List.GetSet.eq.Get.of.Ne.GtLength
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.tensor
open List Tensor


@[main]
private lemma main
  [Zero α]
  {i : Fin s.length}
-- given
  (h_i : i.val > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.resize i n).length = X.length := by
-- proof
  repeat rw [Length.eq.Get_0.of.GtLength_0]
  ·
    rw [GetSet.eq.Get.of.Ne.GtLength (by grind)]
    grind
  ·
    grind


-- created on 2026-07-13
