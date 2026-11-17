module

public import Theorem.Nat.Le_Sub_1
public import Theorem.Nat.Lt.is.Le.Ne

public section

open Nat


public theorem Nat.Val.lt.Sub_1.of.Val.ne.Sub_1
  {i : Fin n}
-- given
  (h : i.val ≠ n - 1) :
-- imply
  i.val < n - 1 := by
-- proof
  have := Le_Sub_1 i
  apply Lt.of.Le.Ne this h


-- created on 2025-06-18
