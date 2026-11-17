module

public import Def.Data.List.List.Basic

public section

public theorem List.EqLengthArraySlice.of.GeLength_Add
  {s : List α}
  {i d : ℕ}
-- given
  (h : s.length ≥ i + d) :
-- imply
  (s.array_slice i d |>.length) = d := by
-- proof
  simp [List.array_slice]
  grind


-- created on 2024-07-01
-- updated on 2026-10-26
