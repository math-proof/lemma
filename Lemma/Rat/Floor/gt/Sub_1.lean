import Lemma.Set.In_IcoFloor
import Lemma.Int.LtSub.is.Lt_Add
open Set Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α) :
-- imply
  ⌊x⌋ > x - 1 := by
-- proof
  have h := In_IcoFloor x
  apply LtSub.of.Lt_Add h.right


-- created on 2025-09-30
