module

public import Mathlib
public import Initialize.Tactic.Attr.Basic


public section

public theorem Nat.EqCast_1'1
  [AddMonoidWithOne R] :
-- imply
  Nat.cast (R := R) 1 = 1 :=
-- proof
  Nat.cast_one


-- created on 2025-06-08
