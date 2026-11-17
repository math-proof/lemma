module

public import Theorem.Nat.EqAdd_Sub.of.Ge
public import Theorem.Nat.Ge.of.Gt

public section

open Nat


public theorem Nat.EqAdd_Sub.of.Gt
  {n m : ℕ}
-- given
  (h : n > m) :
-- imply
  m + (n - m) = n := by
-- proof
  apply EqAdd_Sub.of.Ge
  apply Ge.of.Gt h


-- created on 2025-06-21
