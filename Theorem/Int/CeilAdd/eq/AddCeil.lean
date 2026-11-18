module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Int.CeilAdd.eq.AddCeil
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α)
  (d : ℤ) :
-- imply
  ⌈x + d⌉ = ⌈x⌉ + d :=
-- proof
  Int.ceil_add_intCast x d


-- created on 2025-03-04
