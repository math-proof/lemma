import Lemma.Nat.EqAddMul_Div
open Nat


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n d : Z) :
-- imply
  n / d * d + n % d = n := by
-- proof
  have := EqAddMul_Div n d
  grind


-- created on 2025-03-15
-- updated on 2025-11-16
