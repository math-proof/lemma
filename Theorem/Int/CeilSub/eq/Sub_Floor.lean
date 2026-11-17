module

public import Theorem.Int.CeilAdd.eq.Add_Ceil
public import Theorem.Int.CeilNeg.eq.NegFloor
public import Theorem.Int.Sub.eq.Add_Neg

public section

open Int


public theorem Int.CeilSub.eq.Sub_Floor
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  -- given
  (d : ℤ)
  (x : α) :
-- imply
  ⌈d - x⌉ = d - ⌊x⌋ := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [CeilAdd.eq.Add_Ceil]
  rw [CeilNeg.eq.NegFloor]
  rw [Add_Neg.eq.Sub]


-- created on 2025-11-07
