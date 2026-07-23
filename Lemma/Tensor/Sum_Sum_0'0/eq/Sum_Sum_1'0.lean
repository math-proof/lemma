import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.Sum_Sum
import Lemma.Tensor.Sum_Sum_0'0.as.Sum_Sum_1'0
open Bool Tensor


@[main, comm]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α [m, n]) :
-- imply
  (X.sum 0).sum 0 = (X.sum 1).sum 0 := by
-- proof
  apply Eq.of.SEq
  apply Sum_Sum_0'0.as.Sum_Sum_1'0 (by grind)


-- created on 2026-07-23
