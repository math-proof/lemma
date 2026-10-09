import sympy.functions.elementary.integers
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.Le.of.Lt
open Nat


@[path]
private lemma main
  [IntegerRing Z]
  {d : Z}
-- given
  (h : d > 0)
  (n : Z) :
-- imply
  n % d ≤ d := by
-- proof
  apply Le.of.Lt 
  apply LtMod.of.Gt_0 h n


-- created on 2025-10-14
