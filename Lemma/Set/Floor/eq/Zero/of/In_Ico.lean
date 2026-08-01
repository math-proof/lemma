import Lemma.Set.EqFloor.of.In_Ico
open Set Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∈ Ico 0 1) :
-- imply
  ⌊x⌋ = 0 := by
-- proof
  apply EqFloor.of.In_Ico (z := 0)
  simpa using h


-- created on 2018-10-21
