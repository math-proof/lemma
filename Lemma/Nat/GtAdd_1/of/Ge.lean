import Lemma.Nat.Lt_Add_1.of.Le
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x ≥ y) :
-- imply
  x + 1 > y :=
-- proof
  Lt_Add_1.of.Le h


-- created on 2025-03-28
-- updated on 2025-05-04
