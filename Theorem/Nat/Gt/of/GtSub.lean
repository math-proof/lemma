module

public import Theorem.Nat.Gt_0.of.Gt
public import Theorem.Nat.Sub.gt.Zero.is.Gt

public section

open Nat


public theorem Nat.Gt.of.GtSub
  {a b c : ℕ}
-- given
  (h : a - b > c) :
-- imply
  a > b := by
-- proof
  have h := Gt_0.of.Gt h
  apply Gt.of.Sub.gt.Zero h


-- created on 2025-05-04
