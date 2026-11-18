module

public import Theorem.Tensor.Length.eq.Get_0.of.GtLength_0
public import Def.Data.Tensor.Defs

public section

open Tensor


public theorem Tensor.Length.eq.Get_0.of.GtLength
-- given
  (h : s.length > n)
  (X : Tensor α s) :
-- imply
  X.length = s[0] := by
-- proof
  exact Length.eq.Get_0.of.GtLength_0 (Nat.zero_lt_of_lt h) X


-- created on 2025-06-25
