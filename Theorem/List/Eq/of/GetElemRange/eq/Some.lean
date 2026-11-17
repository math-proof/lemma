module

public import Theorem.List.GetElemRange.eq.None.of.Ge
public import Theorem.Nat.NotLt.is.Ge
public import Mathlib

public section

open List Nat


public theorem List.Eq.of.GetElemRange.eq.Some
  {n i j : ℕ}
-- given
  (h : (List.range n)[i]? = some j) :
-- imply
  i = j := by
-- proof
  by_cases i < n <;>
    aesop


-- created on 2025-06-02
