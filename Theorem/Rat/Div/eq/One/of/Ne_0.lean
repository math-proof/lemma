module

public import Mathlib
public section


public theorem Rat.Div.eq.One.of.Ne_0
  [GroupWithZero α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a / a = 1 := by
-- proof
  simp [h]


-- created on 2024-07-01
