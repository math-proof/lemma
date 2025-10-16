import Lemma.Set.In_IocCeil
import Lemma.Int.Lt_Add.of.LtSub
open Set Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α) :
-- imply
  ⌈x⌉ < x + 1 := by
-- proof
  have h := In_IocCeil x
  apply Lt_Add.of.LtSub h.left


-- created on 2025-10-01
