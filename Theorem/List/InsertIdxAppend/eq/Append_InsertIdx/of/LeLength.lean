module

public import Theorem.List.InsertIdxAppend.eq.Append_InsertIdx
public import Theorem.Nat.EqAdd_Sub.of.Ge

public section

open List Nat


public theorem List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength
  {a : List α}
-- given
  (h : a.length ≤ i)
  (x : α) :
-- imply
  (a ++ b).insertIdx i x = a ++ b.insertIdx (i - a.length) x := by
-- proof
  have := InsertIdxAppend.eq.Append_InsertIdx a b (i - a.length) x
  rwa [EqAdd_Sub.of.Ge h] at this


-- created on 2025-06-09
