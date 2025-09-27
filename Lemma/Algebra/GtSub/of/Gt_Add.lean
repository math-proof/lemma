import Lemma.Algebra.Lt_Sub.of.LtAdd
open Algebra


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a b c : α}
-- given
  (h : c > a + b) :
-- imply
  c - b > a :=
-- proof
  Lt_Sub.of.LtAdd h


-- created on 2024-11-27
