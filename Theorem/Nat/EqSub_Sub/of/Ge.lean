module

public import Mathlib

public section


public theorem Nat.EqSub_Sub.of.Ge
  {a b : ℕ}
-- given
  (h : a ≥ b) :
-- imply
  a - (a - b) = b :=
-- proof
  Nat.sub_sub_self h


-- created on 2025-06-17
