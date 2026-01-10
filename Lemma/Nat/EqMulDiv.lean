import Lemma.Nat.EqMulDiv.of.Dvd
import sympy.functions.elementary.integers
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {n : Z} :
-- imply
  n / n * n = n := by
-- proof
  apply EqMulDiv.of.Dvd
  simp


-- created on 2026-01-10
