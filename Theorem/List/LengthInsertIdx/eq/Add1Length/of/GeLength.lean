module

public import Theorem.List.LengthInsertIdx.eq.Add_Length_1.of.GeLength
public import Def.Data.List.List.Basic
public import Theorem.Nat.Add

public section

open List Nat


public theorem List.LengthInsertIdx.eq.Add1Length.of.GeLength
  {s : List α}
-- given
  (h : s.length ≥ i)
  (a : α) :
-- imply
  (s.insertIdx i a).length = 1 + s.length := by
-- proof
  rw [LengthInsertIdx.eq.Add_Length_1.of.GeLength h]
  rw [Nat.Add.Comm]


-- created on 2025-06-08
-- updated on 2026-10-26
