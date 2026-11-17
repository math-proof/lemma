module

public import Theorem.List.Drop.eq.ListGet.of.GtLength_0

public section

open List


public theorem List.Drop.eq.ListGet.of.GeLength_1
  {s : List α}
-- given
  (h : s.length ≥ 1) :
-- imply
  s.drop (s.length - 1) = [s[s.length - 1]] := by
-- proof
  apply Drop.eq.ListGet.of.GtLength_0
  omega


-- created on 2026-01-03
