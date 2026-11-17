module
public import Mathlib

public section


public theorem List.ProdTake_1.eq.Get_0.of.GtLength_0
  [Monoid α]
  {s : List α}
-- given
  (h_s : s.length > 0) :
-- imply
  (s.take 1).prod = s[0] := by
-- proof
  aesop


-- created on 2025-07-08
-- updated on 2026-10-26
