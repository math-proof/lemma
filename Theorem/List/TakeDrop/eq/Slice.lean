module

public import Def.Data.List.List.Basic
public import Theorem.Nat.EqSubAdd

public section

open Nat


public theorem List.TakeDrop.eq.Slice
-- given
  (s : List α) :
-- imply
  (s.drop i).take d = s.slice i (i + d) := by
-- proof
  unfold List.slice List.array_slice Function.comp
  rw [EqSubAdd.left]


-- created on 2025-06-18
