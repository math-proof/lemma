module

public import Theorem.Nat.LeMin
public import Theorem.Nat.Gt.of.Gt.Ge

public section

open Nat


public theorem Nat.Gt_Min.of.Gt
  [LinearOrder α]
-- given
  (h : c > a)
  (b : α) :
-- imply
  c > a ⊓ b := by
-- proof
  have := LeMin.left a b
  apply Gt.of.Gt.Ge h this


-- created on 2025-05-14
