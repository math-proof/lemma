module

public import Theorem.Nat.Add
public import Theorem.Int.CeilAdd.eq.AddCeil

public section

open Nat Int


public theorem Int.CeilAdd.eq.Add_Ceil
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℤ} :
-- imply
  ⌈d + x⌉ = d + ⌈x⌉ := by
-- proof
  rw [Add.comm]
  rw [CeilAdd.eq.AddCeil]
  rw [Add.comm]


-- created on 2025-03-15
