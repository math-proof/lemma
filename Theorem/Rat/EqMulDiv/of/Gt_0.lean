module

public import Theorem.Rat.EqMulDiv.of.Ne_0
public import Theorem.Nat.Ne.of.Gt

public section

open Nat Rat


public theorem Rat.EqMulDiv.of.Gt_0
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {b : α}
-- given
  (h : b > 0)
  (a : α) :
-- imply
  a / b * b = a := by
-- proof
  have h := Ne.of.Gt h
  apply EqMulDiv.of.Ne_0 h


-- created on 2025-05-04
