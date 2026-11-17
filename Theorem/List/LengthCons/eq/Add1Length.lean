module

public import Theorem.List.LengthCons.eq.AddLength_1
public import Theorem.Nat.Add

public section

open List Nat


public theorem List.LengthCons.eq.Add1Length
-- given
  (a : α)
  (l : List α) :
-- imply
  (a :: l).length = 1 + l.length := by
-- proof
  have := LengthCons.eq.AddLength_1 a l
  rwa [Nat.Add.Comm] at this


-- created on 2025-05-08
-- updated on 2026-07-11
