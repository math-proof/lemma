import Lemma.Nat.GtAddS.is.Gt
open Nat


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c : α}
-- given
  (h : a - b > c) :
-- imply
  a > c + b := by
-- proof
  have h := GtAddS.of.Gt b h
  simp at h
  exact h


-- created on 2024-11-26
