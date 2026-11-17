module

public import Theorem.Nat.LeMin
public import Theorem.Nat.Ge.of.Ge.Ge

public section

open Nat


public theorem Nat.Ge_Min.of.Ge
  [LinearOrder α]
-- given
  (h : c ≥ a)
  (b : α) :
-- imply
  c ≥ a ⊓ b := by
-- proof
  have := LeMin.left a b
  apply Ge.of.Ge.Ge h this


-- created on 2025-05-14
