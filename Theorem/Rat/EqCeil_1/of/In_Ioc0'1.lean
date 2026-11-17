module

public import Theorem.Set.EqCeil.of.In_Ioc

public section

open Set


public theorem Rat.EqCeil_1.of.In_Ioc0'1
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∈ Ioc 0 1) :
-- imply
  ⌈x⌉ = 1 := by
-- proof
  apply EqCeil.of.In_Ioc
  simp
  assumption


-- created on 2025-05-04
