import Lemma.Basic


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x ≥ y) :
-- imply
  -x ≤ -y := by
-- proof
  apply neg_le_neg h


-- created on 2025-03-29
-- updated on 2025-04-04
