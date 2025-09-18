import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  0 % n = 0 :=
-- proof
  IntegerRing.zero_mod n


-- created on 2025-07-11
