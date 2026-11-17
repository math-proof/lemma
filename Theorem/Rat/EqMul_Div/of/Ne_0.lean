module

public import Theorem.Rat.EqMulDiv.of.Ne_0
public import Theorem.Nat.Mul

public section

open Nat Rat


public theorem Rat.EqMul_Div.of.Ne_0
  [CommGroupWithZero α]
-- given
  (h : a ≠ 0)
  (b : α) :
-- imply
  a * (b / a) = b := by
-- proof
  rw [Mul.comm]
  apply EqMulDiv.of.Ne_0 h


-- created on 2025-04-02
