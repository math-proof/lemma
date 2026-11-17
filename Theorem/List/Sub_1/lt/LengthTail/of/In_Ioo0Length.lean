module

public import Theorem.Data.Set.Sets
public import Theorem.Nat.LtSubS.of.Lt.Le

public section

open Nat


public theorem List.Sub_1.lt.LengthTail.of.In_Ioo0Length
  {i : ℕ}
  {s : List α}
-- given
  (h : i ∈ Ioo 0 s.length) :
-- imply
  i - 1 < s.tail.length := by
-- proof
  simp
  apply LtSubS.of.Lt.Le h.1 h.2


-- created on 2025-06-22
-- updated on 2026-10-26
