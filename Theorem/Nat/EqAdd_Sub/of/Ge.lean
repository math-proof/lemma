module

public import Theorem.Nat.EqAddSub.of.Ge
public import Theorem.Nat.Add

public section

open Nat


public theorem Nat.EqAdd_Sub.of.Ge
  {n m : ℕ}
-- given
  (h : n ≥ m) :
-- imply
  m + (n - m) = n := by
-- proof
  rw [Nat.Add.Comm]
  apply EqAddSub.of.Ge h


-- created on 2025-05-09
-- updated on 2025-06-08
