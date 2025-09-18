import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x < y) :
-- imply
  x + 1 ≤ y :=
-- proof
  IntegerRing.succ_le_of_lt h


-- created on 2024-07-01
