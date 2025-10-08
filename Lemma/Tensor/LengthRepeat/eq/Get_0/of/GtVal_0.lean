import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Nat.Gt_0
import Lemma.List.GetSet.eq.Get.of.Ne.Lt_Length
open Tensor List Nat


@[main]
private lemma main
  {d : Fin s.length}
-- given
  (h : d.val > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat n d).length = s[0] := by
-- proof
  rw [Length.eq.Get_0.of.GtLength_0] <;>
    simp
  ·
    rw [GetSet.eq.Get.of.Ne.Lt_Length]
    linarith
  ·
    apply Gt_0
    trivial


-- created on 2025-07-05
