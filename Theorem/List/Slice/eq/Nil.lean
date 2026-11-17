module

public import Def.Data.List.List.Basic
public import Theorem.List.Slice.eq.Nil.of.Ge

public section

open List


public theorem List.Slice.eq.Nil
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.slice i i = .nil := by
-- proof
  apply Slice.eq.Nil.of.Ge
  simp


-- created on 2025-06-10
