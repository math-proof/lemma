import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n < n + 1 :=
-- proof
  IntegerRing.lt_succ_self n


-- created on 2025-08-13
