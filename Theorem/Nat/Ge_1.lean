module

public import Mathlib

public section


public theorem Nat.Ge_1
-- given
  (i : Fin n) :
-- imply
  n ≥ 1 := by
-- proof
  have := i.isLt
  linarith


-- created on 2025-06-07
