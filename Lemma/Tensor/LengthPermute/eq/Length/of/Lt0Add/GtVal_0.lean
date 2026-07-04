import Lemma.List.GetPermute.eq.Get.of.Gt.GtAdd
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open List Tensor


@[main]
private lemma main
  {i : Fin s.length}
  {d : ℤ}
-- given
  (h_i : i.val > 0)
  (h_d : i + d > 0)
  (X : Tensor α s) :
-- imply
  (X.permute i d).length = X.length := by
-- proof
  repeat rw [Length.eq.Get_0.of.GtLength_0]
  ·
    rw [GetPermute.eq.Get.of.Gt.GtAdd h_d h_i]
  ·
    simp
    grind


-- created on 2026-07-04
