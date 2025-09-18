import sympy.functions.elementary.integers
import Lemma.Algebra.NotOdd.is.Mod_2.eq.Zero
open Algebra


@[main, comm, mp, mpr]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n isn't odd ↔ n is even := by
-- proof
  rw [NotOdd.is.Mod_2.eq.Zero, IntegerRing.even_iff]


-- created on 2025-08-13
