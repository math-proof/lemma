module

public import Mathlib
public section


public theorem Rat.EqMulDiv.of.Ne_0
  [GroupWithZero α]
  {b : α}
-- given
  (h : b ≠ 0)
  (a : α) :
-- imply
  a / b * b = a := by
-- proof
  simp [h]


-- created on 2025-03-30
