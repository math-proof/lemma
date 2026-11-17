module

public import Def.Data.List.List.Basic
public import Theorem.Nat.Sub_Add.eq.SubSub
public import Theorem.Nat.EqSubAdd

public section

open Nat


public theorem List.SliceDrop.eq.Slice_AddS
-- given
  (s : List α)
  (n i j : ℕ) :
-- imply
  (s.drop n).slice i j = s.slice (n + i) (n + j) := by
-- proof
  unfold List.slice List.array_slice Function.comp
  simp
  repeat rw [Sub_Add.eq.SubSub]
  rw [EqSubAdd.left]


-- created on 2025-06-17
