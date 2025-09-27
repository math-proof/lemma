import Lemma.Algebra.LeAddS.is.Le
open Algebra


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x - y ≤ 0) :
-- imply
  x ≤ y := by
-- proof
  have := LeAddS.of.Le y h
  simp at this
  assumption


-- created on 2025-03-30
-- updated on 2025-04-30
