module

public import Theorem.Int.CeilSub.eq.Sub_Floor

public section

open Int


public theorem Nat.CeilSub.eq.Sub_Floor
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
