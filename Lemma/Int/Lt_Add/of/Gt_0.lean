import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.EqAdd0
open Nat


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b : α}
-- given
  (h : a > 0) :
-- imply
  b < a + b := by
-- proof
  have := GtAddS.of.Gt b h
  rwa [EqAdd0] at this


-- created on 2025-10-16
