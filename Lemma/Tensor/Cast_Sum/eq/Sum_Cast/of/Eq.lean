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


@[main]
private lemma fin
  [AddCommMonoid α]
-- given
  (h : s = s')
  (X : Fin n → Tensor α s) :
-- imply
  let h := congrArg (Tensor α) h
  cast h (∑ i : Fin n, X i) = ∑ i : Fin n, cast h (X i) :=
-- proof
  main h _ X


-- created on 2025-11-07
