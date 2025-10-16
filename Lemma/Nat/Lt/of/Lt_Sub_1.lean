import Lemma.Nat.LeSub_1
import Lemma.Algebra.Lt.of.Lt.Le
open Algebra Nat


@[main]
private lemma main
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x < y - 1) :
-- imply
  x < y := by
-- proof
  apply Lt.of.Lt.Le h
  apply LeSub_1 y


-- created on 2025-06-02
