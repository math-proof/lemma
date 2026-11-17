module

public section


public theorem List.Take.eq.AppendTake.of.GtLength
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s.take (i + 1) = s.take i ++ [s[i]] := by
-- proof
  simp


-- created on 2025-10-27
