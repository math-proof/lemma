module

public import Mathlib
public section


public theorem Int.EqToNat_0.of.Le_0
  {n : ℤ}
-- given
  (h : n ≤ 0) :
-- imply
  n.toNat = 0 :=
-- proof
  Int.toNat_of_nonpos h


-- created on 2025-05-05
