module

public import Theorem.Nat.LeAdd_1.of.Lt

public section

open Nat


public theorem Nat.Ge_1.of.Gt_0
  [IntegerRing Z]
  {x : Z}
-- given
  (h : x > 0) :
-- imply
  x ≥ 1 := by
-- proof
  have := IntegerRing.succ_le_of_lt h
  simp_all


-- created on 2025-05-24
