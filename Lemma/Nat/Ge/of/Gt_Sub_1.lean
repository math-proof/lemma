import Lemma.Nat.Le.of.LtSub_1
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : y > x - 1) :
-- imply
  y ≥ x :=
-- proof
  Le.of.LtSub_1 h


-- created on 2025-05-05
-- updated on 2025-05-06
