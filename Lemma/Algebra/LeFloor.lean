import Lemma.Set.In_IcoFloor
open Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌊x⌋ ≤ x := by
-- proof
  have := In_IcoFloor (x := x)
  exact this.left


-- created on 2025-05-04
