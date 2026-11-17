module

public import Theorem.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
public import Theorem.List.TakeCons.eq.List
public import Theorem.List.DropTake.eq.TakeDrop

public section

open List


public theorem List.DropTake.eq.ListGet.of.GtLength
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  (s.take (i + 1)).drop i = [s[i]] := by
-- proof
  rw [DropTake.eq.TakeDrop]
  simp
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength (by assumption)]
  rw [TakeCons.eq.List]


-- created on 2025-06-14
-- updated on 2025-06-20
