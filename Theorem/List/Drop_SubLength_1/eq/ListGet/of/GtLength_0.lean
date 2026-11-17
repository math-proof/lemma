module

public import Theorem.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
public import Theorem.Nat.EqAddSub.of.Ge
public import Theorem.List.Drop.eq.Nil

public section

open List Nat


public theorem List.Drop_SubLength_1.eq.ListGet.of.GtLength_0
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.drop (s.length - 1) = [s[s.length - 1]] := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength (by simp_all)]
  rw [EqAddSub.of.Ge (by linarith)]
  rw [Drop.eq.Nil]


-- created on 2025-06-17
