module

public import Theorem.Nat.Le_Sub.is.LeAdd.of.Le
public import Theorem.Nat.Sub.eq.Zero.of.Lt

public section

open Nat


public theorem Nat.LtSub.of.Lt
  {j n : ℕ}
-- given
  (h : j < n)
  (i : ℕ):
-- imply
  j - i < n := by
-- proof
  exact Nat.lt_of_le_of_lt (Nat.sub_le j i) h


-- created on 2025-06-21
