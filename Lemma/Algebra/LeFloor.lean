import Lemma.Set.In_IcoFloor
open Set


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α) :
-- imply
  ⌊x⌋ ≤ x := by
-- proof
  have := In_IcoFloor x
  exact this.left


-- created on 2025-05-04
-- updated on 2025-10-01
