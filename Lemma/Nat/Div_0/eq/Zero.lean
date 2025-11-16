import sympy.Basic
import sympy.functions.elementary.integers


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (a : Z) :
-- imply
  a / 0 = 0 :=
-- proof
  IntegerRing.div_zero a


-- created on 2025-11-16
