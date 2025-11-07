import Lemma.Int.CeilNeg.eq.NegFloor
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌊x⌋ = -⌈-x⌉ := by
-- proof
  simp [CeilNeg.eq.NegFloor]


-- created on 2025-11-07
