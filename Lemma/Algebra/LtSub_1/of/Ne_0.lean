import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  [IntegerRing Z]
  {n : Z}
-- given
  (h : n ≠ 0) :
-- imply
  n - 1 < n :=
-- proof
  IntegerRing.pred_lt h


-- created on 2025-08-13
