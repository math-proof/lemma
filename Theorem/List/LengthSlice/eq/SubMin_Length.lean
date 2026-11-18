module

public import Theorem.List.LengthArraySlice.eq.Min_SubLength
public import Theorem.Nat.SubMin.eq.MinSubS

public section

open List Nat


public theorem List.LengthSlice.eq.SubMin_Length
-- given
  (s : List α)
  (i j : ℕ) :
-- imply
  (s.slice i j).length = j ⊓ s.length - i := by
-- proof
  unfold List.slice
  rw [LengthArraySlice.eq.Min_SubLength]
  rw [← SubMin.eq.MinSubS]


-- created on 2025-05-13
-- updated on 2025-05-16
