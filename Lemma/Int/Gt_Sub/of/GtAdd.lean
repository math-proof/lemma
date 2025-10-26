import Lemma.Int.LtSub.of.Lt_Add
open Int


@[main]
private lemma left
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c : α}
-- given
  (h : a + b > c) :
-- imply
  b > c - a :=
-- proof
  LtSub.of.Lt_Add.left h


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c : α}
-- given
  (h : a + b > c) :
-- imply
  a > c - b :=
-- proof
  LtSub.of.Lt_Add h


-- created on 2024-11-26
