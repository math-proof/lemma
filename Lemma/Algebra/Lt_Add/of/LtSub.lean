import Lemma.Algebra.LtAddS.is.Lt
open Algebra


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c : α}
-- given
  (h : a - b < c) :
-- imply
  a < c + b := by
-- proof
  have h := LtAddS.of.Lt b h
  simp at h
  exact h


-- created on 2024-11-27
