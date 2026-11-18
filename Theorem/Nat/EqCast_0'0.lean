module

public import Mathlib
public import Initialize.Tactic.Attr.Basic


public section

public theorem Nat.EqCast_0'0
  [AddMonoidWithOne R] :
-- imply
  (Nat.cast (R := R) 0) = 0 :=
-- proof
  Nat.cast_zero


-- created on 2025-06-08
