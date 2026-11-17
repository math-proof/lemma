module

public import Theorem.Nat.Ne.of.Gt
public import Theorem.List.HeadD.eq.Get_0.of.NeLength_0

public section

open List Nat


public theorem List.HeadD.eq.Get_0.of.GtLength_0
  {s : List α}
-- given
  (h : s.length > 0)
  (default : α) :
-- imply
  s.headD default = s[0] := by
-- proof
  have := Ne.of.Gt h
  apply HeadD.eq.Get_0.of.NeLength_0 this


-- created on 2025-05-04
