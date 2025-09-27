import Lemma.Basic


@[main]
private lemma left
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b : α}
-- given
  (h : b + a ≥ b) :
-- imply
  a ≥ 0 := by
-- proof
  simp_all


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b : α}
-- given
  (h : a + b ≥ b) :
-- imply
  a ≥ 0 := by
-- proof
  simp_all


-- created on 2025-05-24
