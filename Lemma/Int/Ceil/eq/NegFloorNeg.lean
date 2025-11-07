import Lemma.Int.FloorNeg.eq.NegCeil
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌈x⌉ = -⌊-x⌋ := by
-- proof
  simp [FloorNeg.eq.NegCeil]


-- created on 2025-03-15
-- updated on 2025-11-07
