module

public import Def.Data.List.List.Basic
public import Theorem.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
public import Theorem.List.Drop.eq.Nil

public section

open List Nat


public theorem List.Drop.eq.ListGet.of.GtLength_0
  {s : List α}
-- given
  (h_s : s.length > 0) :
-- imply
  s.drop (s.length - 1) = [s[s.length - 1]] := by
-- proof
  
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength (by omega)]
  rw [EqAddSub.of.Ge (by omega)]
  rw [Drop.eq.Nil]


-- created on 2025-10-22
