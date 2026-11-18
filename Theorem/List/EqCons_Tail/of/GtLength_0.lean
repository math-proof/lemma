module

public import Initialize.Tactic.Attr.Basic

public import Theorem.List.EqCons_Tail.of.NeLength_0
public import Theorem.Nat.Ne.of.Gt

public section

open List Nat


@[comm]
public theorem List.EqCons_Tail.of.GtLength_0
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s[0] :: s.tail = s := by
-- proof
  have h := Ne.of.Gt h
  apply EqCons_Tail.of.NeLength_0 h



public theorem List.Eq_Cons_Tail.of.GtLength_0
  {s : List α}
  (h : s.length > 0) :
  s = s[0] :: s.tail :=
  (EqCons_Tail.of.GtLength_0 h).symm

-- created on 2025-06-09
-- updated on 2025-06-15
