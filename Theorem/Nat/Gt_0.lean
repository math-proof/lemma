module

public section


public theorem Nat.Gt_0
-- given
  (i : Fin n) :
-- imply
  n > 0 := by
-- proof
  have := i.isLt
  linarith


-- created on 2025-06-07
