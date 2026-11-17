module

public section


public theorem Nat.Ne_0.of.Gt
  {a b : ℕ}
-- given
  (h : a > b) :
-- imply
  a ≠ 0 := by
-- proof
  linarith [h]


-- created on 2020-09-21
