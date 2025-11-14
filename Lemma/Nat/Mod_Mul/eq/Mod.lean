import sympy.Basic
import sympy.functions.elementary.integers


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (k m n : Z) :
-- imply
  k % (m * n) % n = k % n :=
-- proof
  IntegerRing.mod_mul


-- created on 2025-11-14
