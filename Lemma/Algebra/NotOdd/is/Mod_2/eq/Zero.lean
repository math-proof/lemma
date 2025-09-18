import sympy.functions.elementary.integers
import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n isn't odd ↔ n % 2 = 0 := by
-- proof
  rw [IntegerRing.odd_iff]
  apply IntegerRing.mod_two_ne_one


-- created on 2025-08-13
