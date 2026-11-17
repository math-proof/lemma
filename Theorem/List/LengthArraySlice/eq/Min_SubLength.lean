module

public import Theorem.List.EqLengthArraySlice.of.LtLength_Add
public import Theorem.List.EqLengthArraySlice.of.GeLength_Add

public section

open List


public theorem List.LengthArraySlice.eq.Min_SubLength
  {s : List α}
  {i n : ℕ} :
-- imply
  (s.array_slice i n).length = n ⊓ (s.length - i) := by
-- proof
  if h : i + n ≤ s.length then
    rw [EqLengthArraySlice.of.GeLength_Add]
    repeat grind
  else
    rw [EqLengthArraySlice.of.LtLength_Add]
    repeat grind


-- created on 2025-05-13
