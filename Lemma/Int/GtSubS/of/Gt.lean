import Lemma.Algebra.LtSubS.of.Lt
open Algebra


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x > y)
  (z : α) :
-- imply
  x - z > y - z :=
-- proof
  LtSubS.of.Lt h z


-- created on 2024-07-01
