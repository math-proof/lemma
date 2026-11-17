module

public import Theorem.Nat.Ge.of.Gt
public import Theorem.List.EqLengthArraySlice.of.LeLength_Add

public section

open List Nat


public theorem List.EqLengthArraySlice.of.LtLength_Add
  {s : List α}
  {i d : ℕ}
-- given
  (h : s.length < i + d) :
-- imply
  (s.array_slice i d).length = s.length - i := by
-- proof
  have h := Ge.of.Gt h
  apply EqLengthArraySlice.of.LeLength_Add h


-- created on 2025-05-13
