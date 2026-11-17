module

public import Theorem.Nat.LeMin
public import Theorem.Nat.Lt.of.Lt.Le

public section

open Nat


public theorem Nat.Lt.of.Lt_Min
  [LinearOrder α]
  {a b : α}
-- given
  (h : x < a ⊓ b) :
-- imply
  x < b := by
-- proof
  have h_le := LeMin a b
  apply Lt.of.Lt.Le h h_le


-- created on 2020-01-11
