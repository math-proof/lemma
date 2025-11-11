import Lemma.Bool.EqCast.of.SEq
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.Tensor.Lt_Length.of.GtLength_0
import Lemma.Tensor.SEqStack_Get.of.GtLength_0
import sympy.tensor.stack
open Bool List Tensor


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  [i < s[0]] X[i]'(Lt_Length.of.GtLength_0 h X i) = cast (by rw [EqCons_Tail.of.GtLength_0 h]) X := by
-- proof
  apply Eq_Cast.of.SEq
  apply SEqStack_Get.of.GtLength_0 h


-- created on 2025-11-11
