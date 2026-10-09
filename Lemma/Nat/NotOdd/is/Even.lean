import sympy.functions.elementary.integers
import Lemma.Nat.NotOdd.is.Mod_2.eq.Zero
open Nat


@[path, comm, mp, mpr]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n isn't odd ↔ n is even := by
-- proof
  rw [NotOdd.is.Mod_2.eq.Zero, IntegerRing.even_iff]


-- created on 2025-08-13
