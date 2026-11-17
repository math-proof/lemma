module

public import Theorem.List.DropTake.eq.ListGet.of.GtLength

public section

open List


public theorem List.DropTake.eq.ListGet
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  (s.take (i + 1)).drop i = [s[i]] := by
-- proof
  apply DropTake.eq.ListGet.of.GtLength


-- created on 2025-10-27
