import Lemma.Set.In_IcoFloor
open Set


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α) :
-- imply
  ⌊x⌋ + 1 > x := by
-- proof
  exact (In_IcoFloor x).right


-- created on 2018-06-17
