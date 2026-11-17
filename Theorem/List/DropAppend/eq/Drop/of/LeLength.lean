module

public import Theorem.List.Drop.eq.Nil.of.LeLength
public import Theorem.List.DropAppend.eq.AppendDropS

public section

open List


public theorem List.DropAppend.eq.Drop.of.LeLength
-- given
  (h : a.length ≤ i)
  (b : List α) :
-- imply
  (a ++ b).drop i = b.drop (i - a.length) := by
-- proof
  rw [DropAppend.eq.AppendDropS]
  rw [Drop.eq.Nil.of.LeLength h]
  simp


-- created on 2025-10-03
