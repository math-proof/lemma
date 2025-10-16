import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma main
  [IntegerRing α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≥ y + 1 :=
-- proof
  IntegerRing.succ_le_of_lt h


-- created on 2024-07-01
