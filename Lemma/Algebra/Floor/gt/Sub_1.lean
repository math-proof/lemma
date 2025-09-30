import Lemma.Set.In_IcoFloor
import Lemma.Algebra.LtSub.of.Lt_Add
open Set Algebra


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
