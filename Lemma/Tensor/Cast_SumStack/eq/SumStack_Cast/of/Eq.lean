import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.SumStack.as.SumStack_Cast.of.Eq
open Bool Tensor


@[main]
private lemma main
  [AddMonoid α]
-- given
  (h : s = s')
  (X : Fin n → Tensor α s) :
-- imply
  let h := congrArg (Tensor α) h
  cast h (∑ i < n, X i) = ∑ i < n, cast h (X i) := by
-- proof
  apply EqCast.of.SEq
  apply SumStack.as.SumStack_Cast.of.Eq h


-- created on 2026-07-22
