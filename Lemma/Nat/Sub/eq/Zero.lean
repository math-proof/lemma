import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (a : Z) :
-- imply
  a - a = 0 :=
-- proof
  IntegerRing.sub_self a


-- created on 2025-10-16
