import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  [IntegerRing Z]
  {a b : Z}
-- given
  (h : a < b) :
-- imply
  a ≤ b - 1 :=
-- proof
  IntegerRing.le_pred_of_lt h


-- created on 2024-07-01
