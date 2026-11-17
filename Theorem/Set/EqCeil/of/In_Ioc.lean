module

public import Theorem.Int.EqCeil.is.Lt.Le
public import Theorem.Set.Lt.of.In_Ioc
public import Theorem.Set.Le.of.In_Ioc

public section

open Set Int


public theorem Set.EqCeil.of.In_Ioc
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {x : α}
-- given
  (h : x ∈ Ioc (z - 1 : α) z) :
-- imply
  ⌈x⌉ = z := by
-- proof
  apply EqCeil.of.Lt.Le
  ·
    exact Lt.of.In_Ioc h
  ·
    exact Le.of.In_Ioc h


-- created on 2018-10-23
