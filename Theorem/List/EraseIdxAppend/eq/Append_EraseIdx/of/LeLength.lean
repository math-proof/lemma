module

public import Theorem.List.EraseIdxAppend.eq.Append_EraseIdx
public import Theorem.Nat.EqAdd_Sub.of.Ge

public section

open List Nat


public theorem List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
  {a : List α}
-- given
  (h : a.length ≤ i)
  (b : List α) :
-- imply
  (a ++ b).eraseIdx i = a ++ b.eraseIdx (i - a.length) := by
-- proof
  have := EraseIdxAppend.eq.Append_EraseIdx a b (i - a.length)
  rwa [EqAdd_Sub.of.Ge (by omega)] at this


-- created on 2025-10-31
