module

public import Mathlib

public section


public theorem Int.Abs.eq.Max_Neg
  [AddGroup α]
  [LinearOrder α]
  {a : α} :
-- imply
  |a| = a ⊔ -a :=
-- proof
  abs_eq_max_neg


-- created on 2025-12-25
