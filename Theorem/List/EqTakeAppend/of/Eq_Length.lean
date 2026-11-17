module

public import Theorem.List.EqTakeAppend

public section

open List


public theorem List.EqTakeAppend.of.Eq_Length
  {a : List α}
-- given
  (h : a.length = n)
  (b : List α) :
-- imply
  (a ++ b).take n = a := by
-- proof
  rw [← h]
  apply EqTakeAppend


-- created on 2025-05-17
