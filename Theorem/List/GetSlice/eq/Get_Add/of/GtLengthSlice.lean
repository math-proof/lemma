module

public import Theorem.List.GetArraySlice.eq.Get_Add.of.GtLength
public import Theorem.List.LengthSlice.eq.SubMin_Length

public section

open List Nat


public theorem List.GetSlice.eq.Get_Add.of.GtLengthSlice
  {s : List α}
-- given
  (h : j < (s.slice i n).length) :
-- imply
  have : i + j < s.length := by
    rw [LengthSlice.eq.SubMin_Length] at h
    apply Lt.of.Lt_Min (LtAdd.of.Lt_Sub.left h)
  (s.slice i n)[j] = s[i + j] := by
-- proof
  unfold List.slice at h ⊢
  apply GetArraySlice.eq.Get_Add.of.GtLength h


-- created on 2025-06-07
-- updated on 2026-08-24
