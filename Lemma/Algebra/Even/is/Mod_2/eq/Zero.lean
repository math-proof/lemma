import sympy.functions.elementary.integers
import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n is even ↔ n % 2 = 0 :=
-- proof
  IntegerRing.even_iff


-- created on 2025-03-05
-- updated on 2025-08-13
