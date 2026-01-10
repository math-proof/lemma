import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma main
  [IntegerRing Z]
  {a : Z}
-- given
  (h : a ≠ 0) :
-- imply
  a / a = 1 :=
-- proof
  IntegerRing.div_self h


-- created on 2026-01-10
