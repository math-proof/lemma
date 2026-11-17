module

public import Instance.Data.Int.Integers

public section


public theorem Int.Sign.eq.Neg1.of.Lt_0
  {x : ℤ}
-- given
  (h : x < 0) :
-- imply
  sign x = -1 :=
-- proof
  Int.sign_eq_neg_one_of_neg h


-- created on 2025-03-30
-- updated on 2026-10-26
