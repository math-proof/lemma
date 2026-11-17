module

public section


public theorem List.EqAppendTake__Drop
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.take i ++ s.drop i = s := by
-- proof
  simp


-- created on 2025-05-09
