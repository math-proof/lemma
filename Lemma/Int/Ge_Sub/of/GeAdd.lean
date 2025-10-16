import Lemma.Int.LeSub.is.Le_Add
open Int


@[main]
private lemma left
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c : α}
-- given
  (h : a + b ≥ c) :
-- imply
  b ≥ c - a :=
-- proof
  LeSub.of.Le_Add.left h


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c : α}
-- given
  (h : a + b ≥ c) :
-- imply
  a ≥ c - b :=
-- proof
  LeSub.of.Le_Add h


-- created on 2024-11-27
-- updated on 2025-10-16
