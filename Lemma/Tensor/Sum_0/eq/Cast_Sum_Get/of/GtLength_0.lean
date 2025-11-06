import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.Lt_Length.of.GtLength_0
import Lemma.Tensor.Sum_0.as.Sum_Get.of.GtLength_0
import sympy.tensor.tensor
open Bool Tensor


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.sum 0 = cast (by simp) (∑ i : Fin s[0], X[i]'(by apply Lt_Length.of.GtLength_0 h)) := by
-- proof
  apply Eq_Cast.of.SEq
  apply Sum_0.as.Sum_Get.of.GtLength_0


@[main]
private lemma fin
  [AddCommMonoid α]
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.sum 0 = cast (by simp) (∑ i : Fin s[0], X.get ⟨i, by apply Lt_Length.of.GtLength_0 h⟩) := by
-- proof
  apply main


-- created on 2025-11-06
