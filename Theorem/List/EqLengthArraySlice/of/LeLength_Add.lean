module

public import Def.Data.List.List.Basic
public import Theorem.Nat.Add

public section

open Nat


public theorem List.EqLengthArraySlice.of.LeLength_Add
  {s : List α}
  {i d : ℕ}
-- given
  (h : s.length ≤ i + d) :
-- imply
  (s.array_slice i d).length = s.length - i := by
-- proof
  simp [List.array_slice]
  rwa [Nat.Add.Comm]


-- created on 2025-05-13
