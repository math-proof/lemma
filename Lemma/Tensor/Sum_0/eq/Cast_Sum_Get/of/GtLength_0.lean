import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.Sum_0.as.Sum_Get.of.GtLength_0
import sympy.tensor.tensor
open Bool Tensor


@[main, fin]
private lemma main
  [AddCommMonoid α]
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.sum 0 = cast (by simp) (∑ i : Fin s[0], X[i]'(GtLength.of.GtLength_0 h X i)) := by
-- proof
  apply Eq_Cast.of.SEq
  apply Sum_0.as.Sum_Get.of.GtLength_0


-- created on 2025-11-06
