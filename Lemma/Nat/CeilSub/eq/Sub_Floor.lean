import Lemma.Int.CeilSub.eq.Sub_Floor
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  -- given
  (d : ℕ)
  (x : α) :
-- imply
  ⌈d - x⌉ = d - ⌊x⌋ := by
-- proof
  simp [← CeilSub.eq.Sub_Floor]


-- created on 2025-11-07
