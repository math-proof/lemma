import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  [IntegerRing Z]
  {d : Z}
-- given
  (h : d > 0)
  (n : Z) :
-- imply
  n % d < d :=
-- proof
  IntegerRing.mod_lt h n


-- created on 2025-03-20
-- updated on 2025-03-29
