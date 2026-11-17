module

public import Theorem.Nat.Lt_Sub.of.LtAdd

public section

open Nat


@[comm]
public theorem List.GetDrop.eq.Get_Add.of.GtLength_Add
  {s : List α}
-- given
  (h : s.length > i + j) :
-- imply
  have : j < (s.drop i).length := by simp_all [Lt_Sub.of.LtAdd.left]
  (s.drop i)[j] = s[i + j] := by
-- proof
  simp_all


-- created on 2025-06-07
-- updated on 2025-06-28
