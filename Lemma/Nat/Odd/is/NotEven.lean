import sympy.functions.elementary.integers
import Lemma.Bool.Iff.is.IffNotS
import Lemma.Nat.NotOdd.is.Even
open Bool Nat


@[main, comm, mp, mpr]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n is odd ↔ n isn't even := by
-- proof
  apply Iff.of.IffNotS
  simp
  apply NotOdd.is.Even


-- created on 2025-08-13
