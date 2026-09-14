import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma main
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x < y) :
-- imply
  x < y + 1 :=
-- proof
  IntegerRing.lt_succ_of_le h.le


-- created on 2019-08-29
