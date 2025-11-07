import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.Sum.as.Sum_Cast.of.Eq
import sympy.tensor.tensor
open Bool Tensor


@[main]
private lemma main
  [AddCommMonoid α]
  [DecidableEq ι]
-- given
  (h : s = s')
  (S : Finset ι)
  (X : ι → Tensor α s) :
-- imply
  let h := congrArg (Tensor α) h
  cast h (∑ i ∈ S, X i) = ∑ i ∈ S, cast h (X i) := by
-- proof
  apply EqCast.of.SEq
  apply Sum.as.Sum_Cast.of.Eq h


-- created on 2025-11-07
