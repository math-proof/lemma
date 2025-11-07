import Lemma.Int.FloorSub.eq.Sub_Ceil
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (d : ℕ)
  (x : α) :
-- imply
  ⌊d - x⌋ = d - ⌈x⌉ := by
-- proof
  simp [← FloorSub.eq.Sub_Ceil]


-- created on 2025-11-07
