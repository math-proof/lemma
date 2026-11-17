module

public import Theorem.List.DropTake.eq.TakeDrop
public import Def.Data.List.List.Basic

public section

open List


public theorem List.Slice.eq.DropTake
-- given
  (s : List α) :
-- imply
  s.slice i j = (s.take j).drop i := by
-- proof
  unfold List.slice List.array_slice
  simp
  rw [← DropTake.eq.TakeDrop]


-- created on 2025-11-28
