import sympy.functions.elementary.integers
import sympy.Basic


@[path, comm, mp, mpr]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n is odd ↔ n % 2 = 1 :=
-- proof
  IntegerRing.odd_iff


-- created on 2025-03-05
-- updated on 2025-08-13
