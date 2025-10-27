import Lemma.Int.LeSubS.is.Le
import Lemma.Nat.LeSubS.of.Le
open Nat Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x ≥ y)
  (z : α) :
-- imply
  x - z ≥ y - z :=
-- proof
  LeSubS.of.Le z h


-- created on 2024-07-01
-- updated on 2025-10-16
