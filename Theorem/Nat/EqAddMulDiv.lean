module

public import Theorem.Nat.EqAddMul_Div
public import Initialize.Tactic.Attr.Basic

public section

open Nat


@[comm]
public theorem Nat.EqAddMulDiv
  [IntegerRing Z]
-- given
  (n d : Z) :
-- imply
  n / d * d + n % d = n := by
-- proof
  have := EqAddMul_Div n d
  grind


-- created on 2025-03-15
-- updated on 2025-11-16
