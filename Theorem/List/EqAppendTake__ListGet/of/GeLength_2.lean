module

public import Theorem.List.Drop.eq.ListGetS.of.GeLength_2
public import Theorem.List.EqAppendTake__Drop

public section

open List


public theorem List.EqAppendTake__ListGet.of.GeLength_2
  {s : List α}
-- given
  (h : s.length ≥ 2) :
-- imply
  s.take (s.length - 2) ++ [s[s.length - 2], s[s.length - 1]] = s := by
-- proof
  rw [ListGetS.eq.Drop.of.GeLength_2 h]
  rw [EqAppendTake__Drop]


-- created on 2026-07-04
