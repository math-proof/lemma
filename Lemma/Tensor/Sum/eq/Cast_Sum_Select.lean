import Lemma.Bool.EqCast.of.SEq
import sympy.tensor.tensor
open Bool


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α s)
  (i : Fin s.length) :
-- imply
  X.sum i = cast (by simp) (∑ k : Fin s[i], X.select i k) := by
-- proof
  apply Eq_Cast.of.SEq
  sorry


-- created on 2025-11-06
