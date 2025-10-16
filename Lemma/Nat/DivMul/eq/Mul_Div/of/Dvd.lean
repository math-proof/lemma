import sympy.functions.elementary.integers
import sympy.Basic


@[main, comm]
private lemma main
  [IntegerRing Z]
  {b c : Z}
-- given
  (h : c ∣ b)
  (a : Z) :
-- imply
  a * b / c = a * (b / c) :=
-- proof
  IntegerRing.mul_div_assoc a h


-- created on 2025-07-08
