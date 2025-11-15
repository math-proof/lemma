import Lemma.Nat.LtAddS.is.Lt
open Nat


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x - y < 0) :
-- imply
  x < y := by
-- proof
  have := LtAddS.of.Lt y h
  simp_all


-- created on 2025-03-24
-- updated on 2025-04-04
