import sympy.functions.elementary.integers
import Lemma.Basic


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n d : Z) :
-- imply
  n = n / d * d + n % d :=
-- proof
  IntegerRing.div_add_mod n d


-- created on 2025-03-15
-- updated on 2025-05-18
