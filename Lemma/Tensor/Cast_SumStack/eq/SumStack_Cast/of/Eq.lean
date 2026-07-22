import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.Sum.as.Sum_Cast.of.Eq
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : s = s')
  (X : Fin n → Tensor α s) :
-- imply
  let h := congrArg (Tensor α) h
  cast h (∑ i < n, X i) = ∑ i < n, cast h (X i) := by
-- proof
  apply EqCast.of.SEq
  apply Sum.as.Sum_Cast.of.Eq h


-- created on 2026-07-22
